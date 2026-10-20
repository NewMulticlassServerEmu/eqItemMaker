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
# INSTRUMENT SONG MODIFIER (bardvalue) - DECISION 2026-10-05
#   This script used to double bardvalue at Enchanted and triple it at Legendary. That is no longer done:
#   bardvalue stays at the base value on every tier. Reason: an instrument's "Focus Effect: <Family>
#   Resonance N" tooltip is a LABEL spell (items.bardeffect) whose N must equal bardvalue - 10 (server
#   manifest v368), and every label spell must also exist in the client's spells_us.txt. Scaling bardvalue
#   here silently breaks those labels and forces a client file change for what should be a data fix.
#   The v421 database regeneration therefore left bardvalue untouched as well. If the song modifier is
#   ever to scale by tier, that is a separate decision: labels, label spells and the client file together.
#
# 2026-10-12 - GENERATOR V2 (supersedes THE FIX above; the v421 curve was reverted by server manifest v622-v661)
#   The v421 curve cut in-game Legendary heroics ~40% and quadrupled attack. The owner restored every tier to its
#   pre-10-05 value and asked for ONE formula that matches the Classic-LoY tiers players know. v2_tiers() below is
#   THJ's old formula, fitted on those 11,452 items (exact on every stat for 70%, 96-99% per stat): core stats,
#   resists, HP, mana, damage x2 (armor with no HP / mana: +5 / +10); endurance and the old stats flat; regen and
#   mana regen x1.5 / x2; haste x1.25 / x1.5; attack = higher of own and 25% / 50% of STR+DEX; spell damage =
#   higher of own and INT (or half WIS), heal amount = higher of own and WIS, Legendary x2; Legendary heroics =
#   base heroic + 25% of the Enchanted stat; Legendary accuracy + 25% of the Enchanted DEX (turned into heroic DEX
#   for ToB). Server manifest v663-v677 applied it in the database: Classic-LoY tiers untouched except where a
#   Legendary stat sat below its Enchanted; LDoN, GoD, LoN, achievements, later eras rebuilt. Afterwards no
#   Legendary anywhere has a stat below its Enchanted (health check row v677).
#
# 2026-10-19 - ITEMS FIT THE ToB CLIENT ITEM RECORD (owner: "fix our items the way ToB actually expects them")
#   The ToB client's item record holds the six resists and seven stats as signed 8-bit (-128..127), elemental damage as
#   unsigned 8-bit (0..255), and has NO heroic resists. Server manifest v748-v756 made every items row fit it (each row's
#   heroic resist added to its own resist, then everything clamped; originals in items_tob_client_limits_original), and
#   the server loader applies the same rule. This script does the same as its LAST step (tob_item_record): the Legendary
#   resist bonus that used to go to heroic_mr/fr/cr/dr/pr now lands in mr/fr/cr/dr/pr (and any base heroic resist, incl.
#   heroic_svcorrup, folds into its resist), every stat and resist is capped at 127 (floored at -128), elemental damage
#   at 255, and no heroic resist is ever written. The bonuses are still worked out from the unclamped Enchanted values,
#   exactly as the rows in the database were, so a regenerated tier equals what v748-v756 left there -- except for the
#   21 base items that carried a heroic resist themselves (2586, 25865, 25866, 900010-900020, 976018-976032): their base
#   row is folded now too, so the doubling starts from the folded value (most of them sit at 127 either way).
#
# 2026-10-19 - NORMAL < ENCHANTED < LEGENDARY (owner; server manifest v762 did the same to every existing item)
#   tier_order() runs after tob_item_record:
#   - a negative stat shrinks per tier: half, at most 5 points per tier (-10 -> -5 -> 0; -50 -> -45 -> -40);
#   - no copy is ever lower than the one below it (Enchanted >= base, Legendary >= Enchanted, delay never slower);
#   - an Enchanted no better than the base gets +B/2 HP and mana (+5% of the base AC) and its Legendary +B (+10% AC);
#     a Legendary no better than its Enchanted gets +B (+10% of the Enchanted AC). B(L) = 10 + 10 * floor((L - 10) / 5).
#     Augments get a small bump instead: A(L) = 5 / 10 / 15 / 20 / 25 (L <= 30 / 50 / 65 / 80 / above), Enchanted +A,
#     Legendary +2A (+A when only the Legendary is short).
#   L = GREATEST(reqlevel, reclevel). An item with no level gets NO bonus here: it is printed as a manual fix (the
#   owner picks the level; never invent one in this script).

# RULE FOR EDITING ITEMS FROM NOW ON
#   Change the BASE item and let the formula derive the tiers (re-run this script with --no-new-only, which only
#   RAISES columns, or the manifest's formula). Do not hand-type stats into a +1000000 / +2000000 row; the health check
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
        # Owner 10-19: never make Enchanted / Legendary copies of ornament augments (ornament slot types 20 / 21, or an
        # augment named "... Ornament"): their tiers had no purpose and were deleted (server manifest v757).
        $query .= " AND NOT (base.itemtype = 54 AND ((base.augtype & (524288 | 1048576)) <> 0 OR base.Name LIKE '%Ornament%'))";
        # Owner 10-19: never tier books (itemclass 2) -- manifest v759 / v760 deleted their copies (and every copy identical to its base;
        # --skip-no-stats, on by default, keeps those from being made again).
        $query .= " AND base.itemclass = 0";
        # Owner 10-19: never tier mounts (click SPA 113) or familiars (click SPA 108); their tiers were deleted (manifest v758).
        $query .= " AND base.clickeffect NOT IN (SELECT id FROM spells_new WHERE 113 IN (effectid1,effectid2,effectid3,effectid4,effectid5,effectid6,effectid7,effectid8,effectid9,effectid10,effectid11,effectid12) OR 108 IN (effectid1,effectid2,effectid3,effectid4,effectid5,effectid6,effectid7,effectid8,effectid9,effectid10,effectid11,effectid12))";
        # Owner 10-20: never tier mercenary items (class bit 0x10000 = class 17, mercenary; the ToB client lets only a
        # mercenary equip them); their 646 copies were deleted (server manifest v780).
        $query .= " AND (base.classes & 65536) = 0";

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
        # Owner 10-19: never tier ornament augments (see above).
        $query .= " AND NOT (itemtype = 54 AND ((augtype & (524288 | 1048576)) <> 0 OR Name LIKE '%Ornament%'))";
        # Owner 10-19: never tier books (see above).
        $query .= " AND itemclass = 0";
        # Owner 10-19: never tier mounts or familiars (see above).
        $query .= " AND clickeffect NOT IN (SELECT id FROM spells_new WHERE 113 IN (effectid1,effectid2,effectid3,effectid4,effectid5,effectid6,effectid7,effectid8,effectid9,effectid10,effectid11,effectid12) OR 108 IN (effectid1,effectid2,effectid3,effectid4,effectid5,effectid6,effectid7,effectid8,effectid9,effectid10,effectid11,effectid12))";
        # Owner 10-20: never tier mercenary items (see above).
        $query .= " AND (classes & 65536) = 0";
        # Owner 10-20: never tier items no player race can use (see above).
        $query .= " AND (races & 65535) <> 0";
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

# Generator v2 (2026-10-12, see the HISTORY NOTE): THJ's old formula, fitted on the Classic-LoY tiers players have,
# with the two choices that keep every Legendary at or above its Enchanted. Both tiers come from the BASE row only.
# Returns (\%enchanted, \%legendary) for the stat columns. Negative base values are kept as they are.
sub v2_tiers {
    my ($b) = @_;
    my $v = sub { my $x = $b->{$_[0]}; return (defined $x && $x ne '') ? $x : 0; };
    my $pos = sub { return $_[0] > 0 ? $_[0] : 0; };
    my (%e, %l);
    foreach my $s (qw(ac astr adex asta aagi aint awis acha hp mana mr fr cr dr pr damage)) {
        $e{$s} = $l{$s} = $v->($s) > 0 ? 2 * $v->($s) : $v->($s);
    }
    if ($v->('itemtype') == 10) {                               # armor with no HP / mana gets a little
        foreach my $s (qw(hp mana)) {
            if ($v->($s) == 0) { $e{$s} = 5; $l{$s} = 10; }
        }
    }
    foreach my $s (qw(endur enduranceregen shielding spellshield dotshielding dsmitigation damageshield strikethrough avoidance stunresist
                      svcorruption heroic_svcorrup elemdmgamt)) {
        $e{$s} = $l{$s} = $v->($s);                             # flat: endurance, the old stats, corruption, elemental damage
    }
    foreach my $s (qw(regen manaregen)) {
        if ($v->($s) > 0) { $e{$s} = int((3 * $v->($s) + 1) / 2); $l{$s} = 2 * $v->($s); }   # x1.5 rounded up, x2
        else { $e{$s} = $l{$s} = $v->($s); }
    }
    if ($v->('haste') > 0) { $e{haste} = int(5 * $v->('haste') / 4); $l{haste} = int(3 * $v->('haste') / 2); }
    else { $e{haste} = $l{haste} = $v->('haste'); }
    $e{accuracy} = $v->('accuracy');
    $l{accuracy} = $pos->($v->('accuracy')) + int(($pos->($e{adex}) + 3) / 4);                # + 25% of the Enchanted DEX
    my $sd = $pos->($v->('astr')) + $pos->($v->('adex'));
    my $q25 = int(($sd + 2) / 4); my $q50 = int(($sd + 1) / 2);
    $e{attack} = $v->('attack') > $q25 ? $v->('attack') : $q25;                                 # higher of own, 25% STR+DEX
    $l{attack} = $e{attack} > $q50 ? $e{attack} : $q50;                                         # higher of that, 50%
    my $from_int = $v->('aint') > 0 ? $v->('aint') : ($v->('awis') > 0 ? int(($v->('awis') + 1) / 2) : 0);
    my $from_wis = $v->('awis') > 0 ? $v->('awis') : 0;
    $e{spelldmg} = $v->('spelldmg') > $from_int ? $v->('spelldmg') : $from_int;                # higher of own and INT (or half WIS)
    $e{healamt}  = $v->('healamt') > $from_wis ? $v->('healamt') : $from_wis;                  # higher of own and WIS
    $l{spelldmg} = 2 * $e{spelldmg};
    $l{healamt}  = 2 * $e{healamt};
    foreach my $pair (["heroic_str","astr"],["heroic_sta","asta"],["heroic_agi","aagi"],["heroic_dex","adex"],["heroic_int","aint"],
                      ["heroic_wis","awis"],["heroic_cha","acha"],["heroic_mr","mr"],["heroic_fr","fr"],["heroic_cr","cr"],["heroic_dr","dr"],["heroic_pr","pr"]) {
        my ($h, $s) = @$pair;
        $e{$h} = $v->($h);
        $l{$h} = $pos->($v->($h)) + int(($pos->($e{$s}) + 3) / 4);                            # base heroic + 25% of the Enchanted stat
    }
    tob_accuracy_to_heroic_dex($_) for (\%e, \%l);
    tob_item_record($_) for (\%e, \%l);                        # fit the ToB client item record (2026-10-19)
    tier_order($b, \%e, \%l);                                  # LAST: normal < Enchanted < Legendary (2026-10-19)
    return (\%e, \%l);
}

# Owner 2026-10-19 (see the header): negatives shrink per tier, no copy below the one under it, and each copy better
# than the one below it (level-scaled HP / mana bonus; small bump for augments). Same rule as server manifest v762.
my %tier_order_reported;
sub tier_order {
    my ($b, $e, $l) = @_;
    my @num = qw(hp mana endur ac damage attack astr asta aagi adex awis aint acha mr fr cr dr pr svcorruption heroic_str
                 heroic_sta heroic_agi heroic_dex heroic_wis heroic_int heroic_cha regen manaregen enduranceregen haste spelldmg
                 healamt elemdmgamt banedmgamt bardvalue);
    my @neg = qw(hp mana endur ac attack astr asta aagi adex awis aint acha mr fr cr dr pr svcorruption heroic_str heroic_sta
                 heroic_agi heroic_dex heroic_wis heroic_int heroic_cha regen manaregen enduranceregen haste spelldmg healamt);
    my $bv = sub { my $x = $b->{$_[0]}; return (defined $x && $x ne '') ? $x : 0; };
    my $tv = sub { my ($t, $f) = @_; return exists $t->{$f} ? ($t->{$f} || 0) : $bv->($f); };
    my $max = sub { my $m = shift; for (@_) { $m = $_ if $_ > $m; } return $m; };
    my $min = sub { return $_[0] < $_[1] ? $_[0] : $_[1]; };
    foreach my $f (@neg) {
        my $n = $bv->($f);
        next unless $n < 0;
        my $step = $min->(int((-$n + 1) / 2), 5);
        $e->{$f} = $max->($tv->($e, $f), $n + $step);
        $l->{$f} = $max->($tv->($l, $f), $min->(0, $n + 2 * $step), $e->{$f});
    }
    foreach my $f (@num) {
        next if $bv->($f) < 0;
        $e->{$f} = $max->($tv->($e, $f), $bv->($f));
        $l->{$f} = $max->($tv->($l, $f), $e->{$f});
    }
    my $bd = $bv->('delay'); my $ed = $tv->($e, 'delay');
    $e->{delay} = $bd if $bd > 0 && $ed > $bd;
    $ed = $tv->($e, 'delay');
    $l->{delay} = $ed if $ed > 0 && $tv->($l, 'delay') > $ed;
    my $better = sub {
        my ($hi, $lo) = @_;   # hashes; a missing column = the base value
        foreach my $f (@num) { return 1 if $hi->($f) > $lo->($f); }
        return 1 if $hi->('delay') > 0 && $hi->('delay') < $lo->('delay');
        return 0;
    };
    my $B = sub { return $bv->($_[0]); };
    my $E = sub { return $tv->($e, $_[0]); };
    my $L = sub { return $tv->($l, $_[0]); };
    my $eb = $better->($E, $B);
    my $le = $better->($L, $E);
    return if $eb && $le;
    my $lvl = $max->($bv->('reqlevel'), $bv->('reclevel'));
    if ($lvl <= 0) {
        print "MANUAL FIX (no level, no tier bonus): $b->{id} $b->{Name}\n" unless $tier_order_reported{$b->{id}}++;
        return;
    }
    my $isaug = ($bv->('itemtype') == 54 || $bv->('augtype') > 0);
    my $add = sub { my ($t, $f, $n) = @_; $t->{$f} = $tv->($t, $f) + $n; };
    if ($isaug) {
        my $a = $lvl <= 30 ? 5 : $lvl <= 50 ? 10 : $lvl <= 65 ? 15 : $lvl <= 80 ? 20 : 25;
        if (!$eb) { $add->($e, $_, $a) for qw(hp mana); $add->($l, $_, 2 * $a) for qw(hp mana); }
        else      { $add->($l, $_, $a) for qw(hp mana); }
        return;
    }
    my $full = 10 + 10 * int(($lvl > 10 ? $lvl - 10 : 0) / 5);
    my $half = int($full / 2);
    if (!$eb) {
        my $bac = $bv->('ac');
        my $eac = $bac > 0 ? $max->(1, ceil($bac * 0.05)) : 0;
        my $ench_ac = $E->('ac');
        my $lac = $ench_ac > 0 ? $max->(ceil($ench_ac * 0.10), $eac + 1) : 0;
        $add->($e, $_, $half) for qw(hp mana); $add->($e, 'ac', $eac);
        $add->($l, $_, $full) for qw(hp mana); $add->($l, 'ac', $lac);
    } else {
        my $ench_ac = $E->('ac');
        $add->($l, $_, $full) for qw(hp mana);
        $add->($l, 'ac', $max->(1, ceil($ench_ac * 0.10))) if $ench_ac > 0;
    }
}

# The ToB client item record (2026-10-19, see the HISTORY NOTE; same rule as server manifest v748-v756 and the server's
# item loader): no heroic resists -- each one is added to its own resist; the six resists and seven stats -128..127;
# elemental damage at most 255. Never writes a heroic resist other than 0.
sub tob_item_record {
    my ($r) = @_;
    my $clamp = sub { my $x = $_[0] || 0; return $x > 127 ? 127 : ($x < -128 ? -128 : $x); };
    foreach my $pair (["mr","heroic_mr"],["fr","heroic_fr"],["cr","heroic_cr"],["dr","heroic_dr"],["pr","heroic_pr"],
                      ["svcorruption","heroic_svcorrup"]) {
        my ($s, $h) = @$pair;
        $r->{$s} = $clamp->(($r->{$s} || 0) + ($r->{$h} || 0));
        $r->{$h} = 0;
    }
    foreach my $s (qw(astr asta aagi adex awis aint acha)) {
        $r->{$s} = $clamp->($r->{$s});
    }
    $r->{elemdmgamt} = 255 if ($r->{elemdmgamt} || 0) > 255;
}

# The ToB client has no Accuracy stat: the server's ToB conversion (manifest v586) turns it into a floor on heroic DEX
# (1 to 3 Accuracy = 1, 4 and up = 1 + ceil(Accuracy / 8)) and sets Accuracy to 0. Done here too, so a newly generated
# tier matches what the conversion gave every existing one.
sub tob_accuracy_to_heroic_dex {
    my ($r) = @_;
    my $a = $r->{accuracy} || 0;
    return if $a <= 0;
    my $s = $a <= 3 ? 1 : 1 + int(($a + 7) / 8);
    $r->{heroic_dex} = $s if $s > ($r->{heroic_dex} || 0);
    $r->{accuracy} = 0;
}

# Calculate expected stats for Enchanted version
sub calculate_enchanted_stats {
    my ($base) = @_;
    my ($e, $l) = v2_tiers($base);
    my %stats = %$e;

    # bardvalue (the instrument song modifier) stays at the base value on every tier (2026-10-05, see the HISTORY
    # NOTE): its tooltip label (items.bardeffect, a 'Resonance N' label spell, N = value - 10) must match it.

    # Set backstabdmg to twice the damage value (only if base item had backstabdmg)
    if (defined $stats{damage} && non_negative($base->{backstabdmg})) {
        $stats{backstabdmg} = $stats{damage} * 2;
    }

    # Adjust proc rate if there's a proc effect
    $stats{procrate} = non_negative($base->{procrate}) ? $base->{procrate} : 0;
    if (non_negative($base->{proceffect}) && $base->{proceffect} > 0) {
        $stats{procrate} += 10;
    }

    return \%stats;
}

# Calculate expected stats for Legendary version. The stat columns come from the base item (v2_tiers); every
# other column is copied from the Enchanted row as before.
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

    my ($e, $l) = v2_tiers($base);
    $stats{$_} = $l->{$_} for keys %$l;

    # Set backstabdmg to twice the damage value (only if base item had backstabdmg)
    if (defined $stats{damage} && non_negative($base->{backstabdmg})) {
        $stats{backstabdmg} = $stats{damage} * 2;
    }

    # bardvalue is not scaled (see calculate_enchanted_stats and the HISTORY NOTE).

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