#!/usr/bin/perl
use warnings;
use strict;
use DBI;
use POSIX qw(ceil);
use JSON;
use Getopt::Long;

# =====================================================================================================
# HISTORY NOTE - 2026-10-05 - Legendary heroic stats bug (fixed below in calculate_legendary_stats)
#
# WHAT WAS WRONG
#   The Legendary step built its row from the Enchanted row (which carries the base item's own heroic
#   stats untouched) and then did
#       $stats{$heroic_stat} = ceil($base->{$normal_stat} * 0.25);
#   The '=' REPLACED the base item's heroic stat with the 25% bonus instead of adding the bonus to it.
#   Any item whose base already has heroic stats (SoF-era and later gear, ~20,500 items) got a
#   Legendary with LOWER heroics than its Enchanted copy. Example, 141490 Jagged Iridescent Sword:
#   base/Enchanted heroic STR 13 -> Legendary heroic STR 6.
#
# HOW IT WAS FOUND
#   Bug report "Shard from Unfathomable Depths (8725) missing legendary stats", then a database audit
#   of all 63,090 base/Enchanted/Legendary triples (claude/notes/item_tiers_audit_2026-10-05/).
#   8,945 of the 9,626 "Legendary heroics below Enchanted" items were this line's output exactly.
#
# WHAT ELSE THE AUDIT FOUND (not this file's fault, but why the data had to be regenerated)
#   An OLDER version of this script had been run on items with ids below ~70,000 and used different
#   rules: Enchanted core stats x1.5 (not x2), Legendary heroics = 25% of the ENCHANTED stat (the old
#   "set to 25% of enchanted" comment below is a leftover of that), a DEX-based Accuracy bonus
#   ("removed per updated rules"), +5/+10 HP and mana on items that had none, and doubled
#   elemental/bane damage. ~600 Legendary rows (the Shard among them) never got the Legendary step at
#   all, so their SD/HA stayed 0 while their Enchanted copy had some. Also, --no-new-only update mode
#   only RAISES a column, so re-running this script never corrected any of that.
#
# THE FIX
#   1) This file: the heroic loop below now ADDS the bonus to the base heroic stat, and the stale
#      "25% of enchanted" comment is corrected. New items generated from here on are right.
#   2) The database: NMS-Server manifest v421 regenerates every tiered wearable item from its base with
#      the formulas in this file (heroics additive), raising AND lowering, so every item sits on one
#      curve. It skips bags, glamours, Hero's Forge, ornament augments, mounts, epics and items THJ
#      hand-edited (a tier gained an effect or changed slots/classes/delay). A permanent health-check
#      row (nms_content_health_check.sql, v421) fails if any in-scope tier ever leaves the curve again.
#
# RULE FOR EDITING ITEMS FROM NOW ON
#   Change the BASE item and let the curve derive the tiers (re-run this script with --no-new-only, or
#   the manifest's formula). Do not hand-type stats into a +1000000 / +2000000 row; the health check
#   will flag it.
# =====================================================================================================

# Default configuration
my $new_only = 1;             # Only create new items by default
my $process_enchanted = 1;    # Process enchanted items by default
my $process_legendary = 1;    # Process legendary items by default
my $skip_no_stats = 1;        # Skip items with no relevant stats
my $exclude_glamour = 1;      # Exclude glamour items
my $batch_size = 1000;        # Default batch size
my $min_id = undef;           # Minimum item ID to process
my $max_id = undef;           # Maximum item ID to process
my $id_list = "";             # Comma-separated list of specific IDs
my $help = 0;                 # Display help

# Process command line arguments
GetOptions(
    "new-only|n!" => \$new_only,          # Flag to only create new items (negatable with --no-new-only)
    "enchanted|e!" => \$process_enchanted, # Flag to process enchanted items
    "legendary|l!" => \$process_legendary, # Flag to process legendary items
    "skip-no-stats|s!" => \$skip_no_stats, # Flag to skip items with no relevant stats
    "exclude-glamour|g!" => \$exclude_glamour, # Flag to exclude glamour items
    "batch-size|b=i" => \$batch_size,     # Batch size for commits
    "min-id|min=i" => \$min_id,           # Minimum item ID
    "max-id|max=i" => \$max_id,           # Maximum item ID
    "ids|i=s" => \$id_list,               # Specific item IDs
    "help|h" => \$help,                   # Display help
) or die("Error in command line arguments\n");

# Display help if requested
if ($help) {
    print_help();
    exit 0;
}

# Validate arguments
if (!$process_enchanted && !$process_legendary) {
    die "Error: You must process at least one type (enchanted or legendary)\n";
}

# Parse ID list if provided
my %specific_ids;
if ($id_list) {
    map { $specific_ids{$_} = 1 } split(/,/, $id_list);
}

sub print_help {
    print <<'HELP';
Item Duplication Script - Creates Enchanted and Legendary versions of items

Usage: perl generate_enchanted_legendary.pl [options]

Options:
  --new-only, -n             Only create new items, don't update existing ones (default: on)
                             Use --no-new-only to also update existing items
  --enchanted, -e            Process Enchanted items (default: on)
                             Use --no-enchanted to skip Enchanted items
  --legendary, -l            Process Legendary items (default: on)
                             Use --no-legendary to skip Legendary items
  --skip-no-stats, -s        Skip items with no relevant stats (default: on)
                             Use --no-skip-no-stats to process all items
  --exclude-glamour, -g      Exclude Glamour items (default: on)
                             Use --no-exclude-glamour to include Glamour items
  --batch-size, -b SIZE      Batch size for commits (default: 1000)
  --min-id, --min MIN        Minimum item ID to process
  --max-id, --max MAX        Maximum item ID to process
  --ids, -i "ID1,ID2,..."    Comma-separated list of specific IDs to process
  --help, -h                 Display this help message

Examples:
  # Process only Enchanted items for IDs 1000-2000
  perl generate_enchanted_legendary.pl --no-legendary --min-id 1000 --max-id 2000

  # Process only Legendary items for specific IDs
  perl generate_enchanted_legendary.pl --no-enchanted --ids "1001,1002,1005,1010"

  # Create and update both types of items
  perl generate_enchanted_legendary.pl --no-new-only
HELP
}

sub LoadMysql {
        use DBI;
        use DBD::mysql;
        use JSON;

        my $json = new JSON();

        #::: Load Config
        my $content;
        open(my $fh, '<', "eqemu_config.json") or die; {
                local $/;
                $content = <$fh>;
        }
        close($fh);

        #::: Decode
        my $config = $json->decode($content);

        #::: Set MySQL Connection vars
        my $db   = $config->{"server"}{"database"}{"db"};
        my $host = $config->{"server"}{"database"}{"host"};
        my $user = $config->{"server"}{"database"}{"username"};
        my $pass = $config->{"server"}{"database"}{"password"};

        #::: Map DSN
        my $dsn = "dbi:mysql:$db:$host:3306";

        #::: Connect and return
        my $connect = DBI->connect($dsn, $user, $pass, {
            mysql_enable_utf8 => 1,
            RaiseError => 1,
            PrintError => 0,
            AutoCommit => 0
        });

        return $connect;
}

# Use the LoadMysql function to get the database handle
my $dbh = LoadMysql();

# Check if successfully connected
unless ($dbh) {
    die "Failed to connect to database.";
}

print "Starting item improvement process...\n";
print "Mode: " . ($new_only ? "New items only" : "Create and update items") . "\n";
print "Processing: " . ($process_enchanted ? "Enchanted " : "") . ($process_legendary ? "Legendary" : "") . "\n";

if ($min_id || $max_id) {
    print "ID Range: " . (defined $min_id ? $min_id : "MIN") . " to " . (defined $max_id ? $max_id : "MAX") . "\n";
}

if ($id_list) {
    print "Processing specific IDs: $id_list\n";
}

# Get the database column names
my $columns_query = $dbh->prepare("SHOW COLUMNS FROM items");
$columns_query->execute();
my @column_names;
while (my $col = $columns_query->fetchrow_hashref()) {
    push @column_names, $col->{Field};
}
$columns_query->finish();

# Counters for tracking progress
my $created_enchanted = 0;
my $created_legendary = 0;
my $updated_enchanted = 0;
my $updated_legendary = 0;
my $skipped_no_stats = 0;
my $processed = 0;
my $batch_count = 0;

# Process Enchanted items if enabled
if ($process_enchanted) {
    process_specific_items('Enchanted');
}

# Process Legendary items if enabled
if ($process_legendary) {
    process_specific_items('Legendary');
}

# Commit any remaining changes
$dbh->commit();

print "\nProcess complete!\n";
print "Processed $processed base items\n";
print "Created $created_enchanted Enchanted, $created_legendary Legendary\n";
if (!$new_only) {
    print "Updated $updated_enchanted Enchanted, $updated_legendary Legendary\n";
}
print "Skipped $skipped_no_stats items with no relevant stats\n";
print "Total modified: " . ($created_enchanted + $created_legendary + $updated_enchanted + $updated_legendary) . " items\n";

$dbh->disconnect();

# Process items for a specific type (Enchanted or Legendary)
sub process_specific_items {
    my ($type) = @_;
    my $id_offset = ($type eq 'Enchanted') ? 1000000 : 2000000;
    
    my $query;
    
    if ($new_only) {
        # In new item only mode, only get items that don't have the special version
        $query = "
            SELECT base.*, 
                   CASE WHEN special.id IS NULL THEN TRUE ELSE FALSE END AS needs_special
            FROM items base
            LEFT JOIN items special ON special.id = base.id + $id_offset
            WHERE base.id < 1000000 
              AND base.slots > 0 
              AND base.classes > 0 
              AND base.races > 0
        ";
        
        # Add ID range conditions if specified
        if (defined $min_id) {
            $query .= " AND base.id >= $min_id";
        }
        if (defined $max_id) {
            $query .= " AND base.id <= $max_id";
        }
        
        # Add specific IDs condition if provided
        if (%specific_ids) {
            $query .= " AND base.id IN (" . join(",", keys %specific_ids) . ")";
        }
        
        if ($exclude_glamour) {
            $query .= " AND base.Name NOT LIKE 'Glamour -%'";
        }
        
        $query .= " HAVING needs_special = TRUE";
    } else {
        # Process all equippable base items when update mode is enabled
        $query = "
            SELECT *
            FROM items 
            WHERE id < 1000000 
              AND slots > 0 
              AND classes > 0 
              AND races > 0
        ";
        
        # Add ID range conditions if specified
        if (defined $min_id) {
            $query .= " AND id >= $min_id";
        }
        if (defined $max_id) {
            $query .= " AND id <= $max_id";
        }
        
        # Add specific IDs condition if provided
        if (%specific_ids) {
            $query .= " AND id IN (" . join(",", keys %specific_ids) . ")";
        }
        
        if ($exclude_glamour) {
            $query .= " AND Name NOT LIKE 'Glamour -%'";
        }
    }
    
    my $items = $dbh->prepare($query);
    $items->execute();
    
    print "Processing items for $type versions...\n";
    
    # Process each base item
    while (my $base_item = $items->fetchrow_hashref()) {
        my $original_id = $base_item->{id};
        my $original_name = $base_item->{Name};
        
        # Check if the item has any of the tracked stats (excluding damage)
        if ($skip_no_stats) {
            my $has_tracked_stats = 0;
            foreach my $stat_field (qw(astr adex asta aagi aint awis acha mr fr cr dr pr ac hp mana endur attack healamt spelldmg bardvalue haste regen manaregen enduranceregen shielding spellshield dotshielding dsmitigation damageshield strikethrough accuracy combateffects avoidance stunresist)) {
                if (defined_and_positive($base_item->{$stat_field})) {
                    $has_tracked_stats = 1;
                    last;
                }
            }
            
            if (!$has_tracked_stats) {
                # Skip items with no tracked stats
                print "Skipping item with no relevant stats: $original_id ($original_name)\n" if $original_id % 100 == 0;
                $skipped_no_stats++;
                $processed++;
                next;
            }
        }
        
        # Calculate the expected Enchanted stats (needed for both types)
        my $enchanted_stats = calculate_enchanted_stats($base_item);
        
        # Choose which stats to use based on type
        my $stats_to_use;
        if ($type eq 'Enchanted') {
            $stats_to_use = $enchanted_stats;
        } else {
            # For Legendary, we need to get the current Enchanted stats
            # if they exist, or calculate what they would be
            my $enchanted_id = $original_id + 1000000;
            my $existing_enchanted_query = $dbh->prepare("SELECT * FROM items WHERE id = ?");
            $existing_enchanted_query->execute($enchanted_id);
            my $existing_enchanted = $existing_enchanted_query->fetchrow_hashref();
            $existing_enchanted_query->finish();
            
            # If Enchanted item exists, use its actual values
            # otherwise use our calculated values
            my $enchanted_data = $existing_enchanted || { %$base_item, %$enchanted_stats };
            
            # Calculate Legendary stats based on Enchanted stats
            $stats_to_use = calculate_legendary_stats($base_item, $enchanted_data);
        }
        
        # Process the special version
        process_special_version($original_id, $original_name, $type, $id_offset, $stats_to_use);
        
        $processed++;
        $batch_count++;
        
        # Commit every batch_size items
        if ($batch_count >= $batch_size) {
            $dbh->commit();
            print "\nCommitted batch. Processed $processed items.\n";
            if ($type eq 'Enchanted') {
                print "Created $created_enchanted Enchanted items\n";
                if (!$new_only) {
                    print "Updated $updated_enchanted Enchanted items\n";
                }
            } else {
                print "Created $created_legendary Legendary items\n";
                if (!$new_only) {
                    print "Updated $updated_legendary Legendary items\n";
                }
            }
            print "Skipped $skipped_no_stats items with no relevant stats\n\n";
            $batch_count = 0;
        }
    }
    
    $items->finish();
    $dbh->commit();
    print "\nCompleted $type items processing.\n";
}

# Calculate expected stats for Enchanted version
sub calculate_enchanted_stats {
    my ($base) = @_;
    my %stats;
    
    # List of stats to be doubled
    my @double_stats = qw(ac astr adex asta aagi aint awis acha hp mana endur mr fr cr dr pr damage bardvalue);
    
    # List of stats to preserve (no scaling)
    my @preserve_stats = qw(haste enduranceregen shielding spellshield dotshielding dsmitigation damageshield strikethrough accuracy combateffects avoidance stunresist);
    
    # List of stats to add 50%
    my @fifty_percent_stats = qw(regen manaregen);
    
    # Double specific stats, ensuring no negative values (round up)
    foreach my $stat (@double_stats) {
        $stats{$stat} = non_negative($base->{$stat}) ? ceil($base->{$stat} * 2) : 0;
    }
    
    # Add 50% to specific stats (round up)
    foreach my $stat (@fifty_percent_stats) {
        $stats{$stat} = non_negative($base->{$stat}) ? ceil($base->{$stat} * 1.5) : 0;
    }
    
    # Preserve stats (copy as is, but ensure non-negative)
    foreach my $stat (@preserve_stats) {
        $stats{$stat} = non_negative($base->{$stat}) ? $base->{$stat} : 0;
    }
    
    # Set backstabdmg to twice the damage value (only if base item had backstabdmg)
    if (defined $stats{damage} && non_negative($base->{backstabdmg})) {
        $stats{backstabdmg} = $stats{damage} * 2;
    }
    
    # +25% of each str and dex to attack (post-doubling)
    if (non_negative($base->{attack})) {
        my $str_bonus = non_negative($stats{astr}) ? ceil($stats{astr} * 0.25) : 0;
        my $dex_bonus = non_negative($stats{adex}) ? ceil($stats{adex} * 0.25) : 0;
        $stats{attack} = ceil($base->{attack} * 2) + $str_bonus + $dex_bonus;
    } else {
        $stats{attack} = 0;
    }
    
    # +50% of int to spelldmg (post-doubling)
    if (non_negative($base->{spelldmg})) {
        my $int_bonus = non_negative($stats{aint}) ? ceil($stats{aint} * 0.5) : 0;
        $stats{spelldmg} = ceil($base->{spelldmg} * 2) + $int_bonus;
    }
    
    # +50% of wis to healamt (post-doubling)
    if (non_negative($base->{healamt})) {
        my $wis_bonus = non_negative($stats{awis}) ? ceil($stats{awis} * 0.5) : 0;
        $stats{healamt} = ceil($base->{healamt} * 2) + $wis_bonus;
    }
    
    # +25% of dex to accuracy (post-doubling) - removed per updated rules
    if (non_negative($base->{accuracy})) {
        $stats{accuracy} = $base->{accuracy}; # Preserve original value
    }
    
    # Adjust proc rate if there's a proc effect
    $stats{procrate} = non_negative($base->{procrate}) ? $base->{procrate} : 0;
    if (non_negative($base->{proceffect}) && $base->{proceffect} > 0) {
        $stats{procrate} += 10;
    }
    
    return \%stats;
}

# Calculate expected stats for Legendary version
sub calculate_legendary_stats {
    my ($base, $enchanted) = @_;
    my %stats;
    
    # Copy all enchanted values first
    foreach my $key (keys %$enchanted) {
        $stats{$key} = $enchanted->{$key};
    }
    
    # Set ID and name properly (these will be overridden later in process_special_version)
    $stats{id} = $base->{id} + 2000000;
    $stats{Name} = $base->{Name} . " (Legendary)";
    
    # Regular stat -> heroic stat pairs. The Legendary heroic stat is the base item's own heroic value
    # PLUS 25% of the base item's regular stat (rounded up). (An older run used 25% of the Enchanted
    # stat; the "set to 25% of enchanted" wording that used to be here described that version.)
    my @heroic_stats = (
        ["astr", "heroic_str"],
        ["adex", "heroic_dex"],
        ["asta", "heroic_sta"],
        ["aagi", "heroic_agi"],
        ["aint", "heroic_int"],
        ["awis", "heroic_wis"],
        ["acha", "heroic_cha"],
        ["mr", "heroic_mr"],
        ["fr", "heroic_fr"],
        ["cr", "heroic_cr"],
        ["dr", "heroic_dr"],
        ["pr", "heroic_pr"]
    );
    
    # Add 25% of base values to heroic stats (round up)
    #
    # BUG FIXED 2026-10-05 (see the HISTORY NOTE at the top of this file). The original loop was:
    #
    #     if (non_negative($base->{$normal_stat})) {
    #         $stats{$heroic_stat} = ceil($base->{$normal_stat} * 0.25);   # '=' replaced the base heroic
    #     } else {
    #         $stats{$heroic_stat} = 0;                                    # and this wiped it outright
    #     }
    #
    # %stats was copied from the Enchanted row, so $stats{$heroic_stat} already held the base item's
    # own heroic stat. Assigning over it meant a Legendary could have LOWER heroics than its Enchanted
    # copy whenever the base item had heroics of its own. The bonus must be ADDED to the base heroic.
    foreach my $pair (@heroic_stats) {
        my ($normal_stat, $heroic_stat) = @$pair;
        my $base_heroic = non_negative($base->{$heroic_stat}) ? $base->{$heroic_stat} : 0;
        my $bonus       = non_negative($base->{$normal_stat}) ? ceil($base->{$normal_stat} * 0.25) : 0;
        $stats{$heroic_stat} = $base_heroic + $bonus;
    }
    
    # List of stats to add additional 50% (double base values)
    my @double_base_stats = qw(regen manaregen);
    
    # List of stats to preserve from enchanted (no additional scaling)
    my @preserve_stats = qw(haste enduranceregen shielding spellshield dotshielding dsmitigation damageshield strikethrough accuracy combateffects avoidance stunresist);
    
    # Add another 50% to these stats (round up)
    foreach my $stat (@double_base_stats) {
        if (non_negative($enchanted->{$stat})) {
            $stats{$stat} = ceil($enchanted->{$stat} * 1.5); # already 1.5x base, now 1.5x that = 2.25x base
        } else {
            $stats{$stat} = 0;
        }
    }
    
    # Preserve these stats from enchanted (which are same as base)
    foreach my $stat (@preserve_stats) {
        $stats{$stat} = non_negative($enchanted->{$stat}) ? $enchanted->{$stat} : 0;
    }
    
    # Double spelldmg, healamt, attack from enchanted (round up)
    if (non_negative($enchanted->{spelldmg})) {
        $stats{spelldmg} = ceil($enchanted->{spelldmg} * 2);
    }
    
    if (non_negative($enchanted->{healamt})) {
        $stats{healamt} = ceil($enchanted->{healamt} * 2);
    }
    
    if (non_negative($enchanted->{attack})) {
        $stats{attack} = ceil($enchanted->{attack} * 2);
    }
    
    # Set backstabdmg to twice the damage value (only if base item had backstabdmg)
    if (defined $stats{damage} && non_negative($base->{backstabdmg})) {
        $stats{backstabdmg} = $stats{damage} * 2;
    }
    
    # Triple bardvalue from base
    if (non_negative($base->{bardvalue})) {
        $stats{bardvalue} = ceil($base->{bardvalue} * 3);
    }
    
    # Adjust proc rate if there's a proc effect
    if (non_negative($base->{proceffect}) && $base->{proceffect} > 0) {
        $stats{procrate} += 10; # +10 additional (on top of the +10 from enchanted)
    }
    
    return \%stats;
}

# Helper to check if a value is defined and positive
sub defined_and_positive {
    my ($value) = @_;
    return defined($value) && $value ne '' && $value > 0;
}

# Helper to check if a value is defined and non-negative
sub non_negative {
    my ($value) = @_;
    return defined($value) && $value ne '' && $value >= 0;
}

# Process a special version (create or update as needed)
sub process_special_version {
    my ($base_id, $base_name, $type, $id_offset, $expected_stats) = @_;
    my $special_id = $base_id + $id_offset;
    my $special_name = $base_name . " ($type)";
    
    if ($new_only) {
        # In new item only mode, we can skip checking for existence since our query
        # already filtered for items that don't have special versions
        
        # Get all the original item details
        my $get_base_stmt = $dbh->prepare("SELECT * FROM items WHERE id = ?");
        $get_base_stmt->execute($base_id);
        my $base_data = $get_base_stmt->fetchrow_hashref();
        $get_base_stmt->finish();
        
        if ($base_data) {
            # Create a copy with modified details
            my %new_item = %$base_data;
            $new_item{id} = $special_id;
            $new_item{Name} = $special_name;
            
            # Apply all the expected stats
            foreach my $stat (keys %$expected_stats) {
                $new_item{$stat} = $expected_stats->{$stat};
            }
            
            # Prepare the INSERT statement with backticks around column names
            my @placeholders;
            my @values;
            my @escaped_columns;
            
            foreach my $column (@column_names) {
                if (exists $new_item{$column}) {
                    push @escaped_columns, "`$column`";
                    push @placeholders, "?";
                    push @values, $new_item{$column};
                }
            }
            
            my $insert_sql = "INSERT INTO items (" . join(", ", @escaped_columns) . ") VALUES (" . join(", ", @placeholders) . ")";
            my $insert_stmt = $dbh->prepare($insert_sql);
            
            $insert_stmt->execute(@values);
            print "Creating $type item: $base_id -> $special_id ($base_name -> $special_name)\n";
            
            if ($type eq 'Enchanted') {
                $created_enchanted++;
            } else {
                $created_legendary++;
            }
        }
    } else {
        # Check if the special version exists
        my $check_stmt = $dbh->prepare("SELECT * FROM items WHERE id = ?");
        $check_stmt->execute($special_id);
        my $special_item = $check_stmt->fetchrow_hashref();
        $check_stmt->finish();
        
        if ($special_item) {
            # Item exists - check if stats need to be updated
            my $updates_needed = 0;
            my %updates;
            
            # Check each expected stat to see if it needs updating
            foreach my $stat (keys %$expected_stats) {
                # Skip undefined values
                next unless defined $special_item->{$stat};
                
                # Compare current with expected, update if current is less
                if ($special_item->{$stat} < $expected_stats->{$stat}) {
                    $updates{$stat} = $expected_stats->{$stat};
                    $updates_needed = 1;
                }
            }
            
            # Update the item if needed
            if ($updates_needed) {
                my @set_clauses;
                my @values;
                my @update_log;
                
                foreach my $stat (sort keys %updates) {
                    push @set_clauses, "`$stat` = ?";
                    push @values, $updates{$stat};
                    push @update_log, "$stat: $special_item->{$stat} -> $updates{$stat}";
                }
                
                my $update_sql = "UPDATE items SET " . join(", ", @set_clauses) . " WHERE id = ?";
                push @values, $special_id;
                
                my $update_stmt = $dbh->prepare($update_sql);
                $update_stmt->execute(@values);
                
                print "Updating $type item: $base_id -> $special_id ($base_name -> $special_name)\n";
                print "  " . join(", ", @update_log) . "\n";
                
                if ($type eq 'Enchanted') {
                    $updated_enchanted++;
                } else {
                    $updated_legendary++;
                }
            }
        } else {
            # Item doesn't exist - create it
            # First get all the original item details
            my $get_base_stmt = $dbh->prepare("SELECT * FROM items WHERE id = ?");
            $get_base_stmt->execute($base_id);
            my $base_data = $get_base_stmt->fetchrow_hashref();
            $get_base_stmt->finish();
            
            if ($base_data) {
                # Create a copy with modified details
                my %new_item = %$base_data;
                $new_item{id} = $special_id;
                $new_item{Name} = $special_name;
                
                # Apply all the expected stats
                foreach my $stat (keys %$expected_stats) {
                    $new_item{$stat} = $expected_stats->{$stat};
                }
                
                # Prepare the INSERT statement with backticks around column names
                my @placeholders;
                my @values;
                my @escaped_columns;
                
                foreach my $column (@column_names) {
                    if (exists $new_item{$column}) {
                        push @escaped_columns, "`$column`";
                        push @placeholders, "?";
                        push @values, $new_item{$column};
                    }
                }
                
                my $insert_sql = "INSERT INTO items (" . join(", ", @escaped_columns) . ") VALUES (" . join(", ", @placeholders) . ")";
                my $insert_stmt = $dbh->prepare($insert_sql);
                
                $insert_stmt->execute(@values);
                print "Creating $type item: $base_id -> $special_id ($base_name -> $special_name)\n";
                
                if ($type eq 'Enchanted') {
                    $created_enchanted++;
                } else {
                    $created_legendary++;
                }
            }
        }
    }
}