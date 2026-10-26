<
------------------------
-- Global variables. This file declares shared variables as local to the scope
-- of the final qw lua source file.

-- All constants go in this table.
local const = {}

-- Plan functions. These must later be initialized as cascades.
local plans = {}

-- All variables past this point are qw state.
local qw = {}

local branch_data = {}
local hell_branches
local portal_data = {}
local god_data = {}
local good_gods

local goal_list
local which_goal = 1
local debug_goal
local goal_status
local goal_branch
local goal_depth
local goal_travel

local early_first_lair_branch
local first_lair_branch_end
local early_second_lair_branch
local second_lair_branch_end
local early_vaults
local vaults_end
local early_zot
local zot_end

local previous_god
local previous_where
local where
local where_branch
local where_depth

local permanent_flight
local gained_permanent_flight
local temporary_flight
local open_runed_doors
local permanent_bazaar
local dislike_pan_level = false

local cache_parity
local check_reachable_features = {}
local feature_map_positions_cache
local feature_map_positions
local item_searches
local item_map_positions_cache
local item_map_positions
local traversal_maps_cache
local traversal_map
local exclusion_maps_cache
local exclusion_map
local distance_maps_cache
local distance_maps

local level_map_mode_searches
local map_mode_searches
local map_mode_search_key
local map_mode_search_hash
local map_mode_search_zone
local map_mode_search_count
local map_mode_search_attempts = 0

local transp_map = {}
local transp_search_zone
local transp_search_count
local transp_zone
local transp_orient
local transp_search

local disable_autoexplore
local last_wait = 0
local wait_count = 0
local hiding_turn_count = -100

local prev_hatch_dist = 1000
local prev_hatch

local stairs_travel

local next_delay = 100

local invis_monster = false
local invis_monster_pos
local invis_monster_turns = 0
local nasty_invis_caster = false

local hostile_summon_timer = -200

local stairdance_count = {}
local clear_exclusion_count = {}
local vaults_end_entry_turn
local tomb2_entry_turn
local tomb3_entry_turn
-----------------------------------------
-- Attack setup and evaluation

const.attack = { "melee", "launcher", "throw", "evoke" }

-- Is the result from an attack on the first target better than the current
-- best result?
function result_improves_attack(attack, result, best_result)
    if not result then
        return false
    end

    if not best_result then
        return true
    end

    return compare_table_keys(result, best_result, attack.props,
        attack.reversed_props)
end

function score_enemy_hit(result, enemy, attack)
    if attack.check and not attack.check(enemy) then
        return
    end

    for _, prop in ipairs(attack.props) do
        local use_min = attack.min_props[prop]
        if not use_min and not result[prop] then
            result[prop] = 0
        end

        if prop == "hit" then
            result[prop] = result[prop] + 1
        elseif use_min then
            local value = enemy[prop](enemy)
            if not result[prop] or value < result[prop] then
                result[prop] = value
            end
        else
            local value = enemy[prop](enemy)
            if value == true then
                value = 1
            elseif value == false then
                value = 0
            end

            result[prop] = result[prop] + value
        end
    end
end

function assess_melee_target(attack, enemy)
    local result = { attack = attack, pos = enemy:pos() }
    score_enemy_hit(result, enemy, attack)
    return result
end

function make_melee_attack(weapons)
    local attack = {
        type = const.attack.melee,
        items = weapons,
        has_damage_rating = true,
        uses_finesse = true,
        uses_heroism = true,
        uses_berserk = true,
        uses_might = true
    }
    attack.props = { "los_danger", "distance", "is_constricting_you",
        "stabbability", "damage_level", "threat", "is_orc_priest_wizard" }
    -- We favor closer monsters.
    attack.reversed_props = { distance = true }
    attack.min_props = { distance = true }

    return attack
end

function make_primary_attack()
    local weapons
    local equip = inventory_equip(const.inventory.equipped)
    if equip then
        weapons = equip.weapon
    end

    if weapons and weapons[1].is_ranged then
        return make_launcher_attack(weapons)
    else
        return make_melee_attack(weapons)
    end
end

function get_primary_target()
    if using_ranged_weapon() then
        return get_launcher_target()
    else
        return get_melee_target()
    end
end


function get_melee_attack()
    local attack = get_attack(1)
    if not attack or attack.type ~= const.attack.melee then
        return
    end

    return attack
end

function get_melee_target_func(assume_flight)
    local attack = get_melee_attack()
    if not attack then
        return
    end

    local best_result
    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:player_can_melee()
                or enemy:get_player_move_towards(assume_flight) then
            local result = assess_melee_target(attack, enemy)
            if result_improves_attack(attack, result, best_result) then
                best_result = result
            end
        end
    end

    return best_result
end

function get_melee_target(assume_flight)
    return turn_memo_args("get_melee_target",
        function()
            return get_melee_target_func(assume_flight)
        end, assume_flight)
end

function assess_explosion_position(attack, target_pos, second_pos)
    local result = { attack = attack, pos = target_pos, positions = {} }
    for pos in adjacent_iter(target_pos, true) do
        result.positions[hash_position(pos)] = true

        if positions_equal(target_pos, const.origin)
                and not attack.explosion_ignores_player then
            return
        end

        local mons
        if supdist(pos) <= qw.los_radius then
            mons = get_monster_at(pos)
        end
        if mons then
            if mons:attitude() > const.attitude.hostile
                    and not mons:ignores_player_projectiles() then
                return
            end

            if mons:is_enemy() then
                score_enemy_hit(result, mons, attack)
            end
        end
    end

    if not second_pos or result.positions[hash_position(second_pos)] then
        return result
    end
end

function assess_ranged_position(attack, target_pos, second_pos)
    if debug_channel("ranged") then
        dsay("Targeting " .. cell_string_from_position(target_pos))
    end

    if secondary_pos
            and attack.is_exploding
            and position_distance(target_pos, secondary_pos) > 2 then
        return
    end

    local positions = spells.path(attack.test_spell, target_pos.x,
        target_pos.y, 0, 0, false)
    local result = { attack = attack, pos = target_pos, positions = {} }
    local past_target, at_target_result
    for i, coords in ipairs(positions) do
        local pos = { x = coords[1], y = coords[2] }
        if position_distance(pos, const.origin) > attack.range then
            break
        end

        local hit_target = positions_equal(pos, target_pos)
        local mons = get_monster_at(pos)
        -- Non-penetrating attacks must reach the target before reaching any
        -- other enemy, otherwise they're considered blocked and unusable.
        if not attack.is_penetrating
                and not past_target
                and not hit_target
                and mons and not mons:ignores_player_projectiles() then
            if debug_channel("ranged") then
                dsay("Aborted target: blocking monster at "
                    .. cell_string_from_position(pos))
            end

            return
        end

        -- Never potentially hit non-enemy monsters that are allies, would get
        -- aggravated, or would cause penance. If at_target_result is defined,
        -- we'll be using '.', otherwise we abort this target.
        if mons and not mons:is_enemy()
                and not mons:is_harmless()
                and not mons:ignores_player_projectiles() then
            if debug_channel("ranged") then
                if at_target_result then
                    dsay("Using at-target key due to non-enemy monster at "
                        .. cell_string_from_position(pos))
                else
                    dsay("Aborted target: non-enemy monster at "
                        .. cell_string_from_position(pos))
                end
            end

            return at_target_result
        end

        -- Unless we're hitting our target right now, try to avoid losing ammo
        -- to destructive terrain at the end of our throw path by using '.'.
        if not hit_target
                and not attack.is_exploding
                and attack.type == const.attack.throw
                and attack.items[1].subtype() ~= "boomerang"
                and i == #positions
                and destroys_items_at(pos)
                and not destroys_items_at(target_pos) then
            if debug_channel("ranged") then
                dsay("Using at-target key due to destructive terrain at "
                    .. pos_string(pos))
            end

            return at_target_result
        end

        result.positions[hash_position(pos)] = true

        if mons and not mons:ignores_player_projectiles() then
            if attack.is_exploding then
                return assess_explosion_position(attack, target_pos,
                    second_pos)
            elseif mons:is_enemy()
                    -- Non-penetrating attacks only get the values from the
                    -- target.
                    and (attack.is_penetrating or hit_target) then
                score_enemy_hit(result, mons, attack)
                if debug_channel("ranged") then
                    dsay("Attack scores after enemy at " .. pos_string(pos)
                        .. ": " .. stringify_table(result))
                end
            end
        end

        -- We've reached the target, so make a copy of the results up to this
        -- point in case we later decide to use '.'.
        if hit_target
                and (not second_pos
                    or result.positions[hash_position(second_pos)]) then
            at_target_result = util.copy_table(result)
            at_target_result.aim_at_target = true
            past_target = true
        end
    end

    -- We never hit anything, so make sure we return nil. This can happen in
    -- rare cases like an eldritch tentacle residing in its portal feature,
    -- which is solid terrain.
    if not result.hit or result.hit == 0 then
        return
    end

    return result
end

function assess_possible_explosion_positions(attack, target_pos, second_pos)
    local best_result
    for pos in adjacent_iter(target_pos, true) do
        local valid, mon
        if supdist(pos) <= qw.los_radius
                and (not attack.seen_pos or not attack.seen_pos[pos.x][pos.y])
                and (attack.explosion_ignores_player
                    or position_distance(pos, const.origin) > 1)
                -- If we have a second position, don't consider explosion
                -- centers that won't reach the position.
                and (not second_pos or position_distance(pos, second_pos) <= 1) then
            valid = true
            mon = get_monster_at(pos)
        end

        if valid and (positions_equal(target_pos, pos)
                or not mon
                or mon:ignores_player_projectiles()) then
            local result = assess_ranged_position(attack, pos, second_pos)
            if result_improves_attack(attack, result, best_result) then
                best_result = result
            end

            if attack.seen_pos then
                attack.seen_pos[pos.x][pos.y] = true
            end
        end
    end
    return best_result
end

function attack_test_spell(attack)
end

function make_launcher_attack(weapons)
    local attack = {
        type = const.attack.launcher,
        items = weapons,
        has_damage_rating = true,
        uses_finesse = true,
        uses_heroism = true,
        range = qw.los_radius,
        can_target_empty = false,
        test_spell = "Quicksilver Bolt",
    }

    for _, weapon in ipairs(weapons) do
        if item_is_penetrating(weapon) then
            attack.is_penetrating = true
        end

        if item_is_exploding(weapon) then
            attack.is_exploding = true

            attack.explosion_ignores_player = true
            if not item_explosion_ignores_player(weapon) then
                attack.explosion_ignores_player = false
            end
        end
    end

    attack.props = { "los_danger", "hit", "distance", "is_constricting_you",
        "damage_level", "threat", "is_orc_priest_wizard" }
    attack.reversed_props = { distance = true }
    attack.min_props = { distance = true }
    return attack
end

function make_throwing_attack(missile, prefer_melee)
    if not missile then
        return
    end

    local attack = {
        type = const.attack.throw,
        items = { missile },
        has_damage_rating = true,
        prefer_melee = prefer_melee,
        uses_finesse = true,
        uses_heroism = true,
        range = qw.los_radius,
        is_penetrating = item_is_penetrating(missile),
        can_target_empty = true,
        test_spell = "Quicksilver Bolt",
    }
    attack.props = { "los_danger", "hit", "distance", "is_constricting_you",
        "damage_level", "threat", "is_orc_priest_wizard" }
    attack.reversed_props = { distance = true }
    attack.min_props = { distance = true }
    return attack
end

function assess_ranged_target(attack, pos, second_pos)
    if position_distance(pos, const.origin) > attack.range
            or not you.see_cell_solid_see(pos.x, pos.y) then
        return
    end

    local result
    if attack.is_exploding and attack.can_target_empty then
        result = assess_possible_explosion_positions(attack, pos, second_pos)
    else
        result = assess_ranged_position(attack, pos, second_pos)
    end

    return result
end

function get_ranged_attack_target(attack)
    if not attack then
        return
    end

    local melee_target
    if attack.prefer_melee then
        melee_target = get_melee_target()
        if melee_target
                and get_monster_at(melee_target.pos):player_can_melee() then
            return
        end
    end

    if attack.is_exploding then
        attack.seen_pos = {}
        for i = -qw.los_radius, qw.los_radius do
            attack.seen_pos[i] = {}
        end
    end

    local best_result
    for _, enemy in ipairs(qw.enemy_list) do
        -- If we have and prefer a melee target and there's a ranged monster,
        -- we'll abort whenever there's a monster we could move towards
        -- instead, since this is how the melee movement plan works.
        if melee_target and enemy:is_ranged() and enemy:get_player_move_towards() then
            return
        end

        local pos = enemy:pos()
        if enemy:distance() <= attack.range
                and you.see_cell_solid_see(pos.x, pos.y) then
            local result
            if attack.is_exploding and attack.can_target_empty then
                result = assess_possible_explosion_positions(attack, pos)
            else
                result = assess_ranged_position(attack, pos)
            end

            if result_improves_attack(attack, result, best_result) then
                best_result = result
            end
        end
    end
    if best_result then
        return best_result
    end
end

function get_best_throwing_attack()
    local attack = get_attack(2)
    if not attack or attack.type ~= const.attack.throw then
        return
    end

    return attack
end

function get_secondary_throwing_attack()
    local attack = get_attack(3)
    if not attack or attack.type ~= const.attack.throw then
        return
    end

    return attack
end

function get_high_threat_target()
    local enemy = get_scary_enemy()
    if not enemy then
        return
    end

    local attack = enemy:best_player_attack()
    if not attack then
        return
    end

    local pos = enemy:pos()
    local primary_target = get_primary_target()
    if attack.type == const.attack.melee then
        if positions_equal(primary_target.pos, pos) then
            return primary_target
        else
            return
        end
    end

    local secondary_pos
    if primary_target and not positions_equal(primary_target.pos, pos) then
        secondary_pos = primary_target.pos
    end

    return assess_ranged_target(attack, pos, secondary_pos)
end

function get_throwing_target_func()
    local target = get_high_threat_target()
    if target then
        if target.attack.type ~= const.attack.throw then
            return
        end

        return target
    end

    if have_moderate_threat()
            and qw.incoming_monsters_turn == you.turns() then
        return
    end

    local attack = get_secondary_throwing_attack()
    if not attack then
        return
    end

    return get_ranged_attack_target(attack)
end

function get_throwing_target()
    return turn_memo("get_throwing_target", get_throwing_target_func)
end

function get_evoke_target()
    return turn_memo("get_evoke_target",
        function()
            local target = get_high_threat_target()
            if target and target.attack.type == const.attack.evoke then
                return target
            end
        end)
end

function get_launcher_target()
    return turn_memo("get_launcher_target",
        function() return get_ranged_attack_target(get_attack(1)) end)
end

function poison_spit_attack()
    local poison_gas = you.mutation("spit poison") > 1
    local attack = {
        range = poison_gas and 6 or 5,
        is_penetrating = poison_gas,
        prefer_melee = not using_ranged_weapon(),
        test_spell = "Quicksilver Bolt",
        props = { "los_danger", "hit", "distance", "is_constricting_you",
            "damage_level", "threat", "is_orc_priest_wizard" },
        reversed_props = { distance = true },
        min_props = { distance = true },
        check = function(mons) return mons:res_poison() < 1 end,
    }
    return attack
end

function make_wand_attack(wand_type)
    local wand = find_item("wand", wand_type)
    if not wand then
        return
    end

    local attack = {
        type = const.attack.evoke,
        items = { wand },
        range = item_range(wand),
        is_penetrating = item_is_penetrating(wand),
        is_exploding = item_is_exploding(wand),
        can_target_empty = item_can_target_empty(wand),
        explosion_ignores_player = item_explosion_ignores_player(wand),
        damage_is_hp = wand_type == "paralysis",
        test_spell = "Quicksilver Bolt",
        props = { "los_danger", "hit", "distance", "is_constricting_you",
            "damage_level", "threat", "is_orc_priest_wizard" },
        reversed_props = { distance = true },
        min_props = { distance = true },
    }
    return attack
end

function get_attacks()
    if qw.attacks then
        return qw.attacks
    end

    local attack = make_primary_attack()
    attack.index = 1
    qw.attacks = { attack }

    attack = make_throwing_attack(best_missile(missile_damage))
    if attack then
        table.insert(qw.attacks, attack)
        attack.index = #qw.attacks
    end

    attack = make_throwing_attack(best_missile(missile_quantity), true)
    if attack then
        table.insert(qw.attacks, attack)
        attack.index = #qw.attacks
    end

    for _, wand_type in ipairs(const.wand_types) do
        attack = make_wand_attack(wand_type)
        if attack then
            table.insert(qw.attacks, attack)
            attack.index = #qw.attacks
        end
    end

    return qw.attacks
end

function get_attack(index)
    local attacks = get_attacks()
    return attacks[index]
end

function get_ranged_target()
    return turn_memo("get_ranged_target",
        function()
            if you.berserk() then
                return false
            end

            local target = get_evoke_target()
            if target then
                return target
            end

            target = get_throwing_target()
            if target then
                return target
            end

            if using_ranged_weapon() then
                return get_launcher_target()
            end
        end)
end

function have_target()
    if get_primary_target() then
        return true
    end

    return get_throwing_target()
end

function get_ranged_attack()
    if using_ranged_weapon() then
        return get_attack(1)
    end

    return get_best_throwing_attack()
end

function make_damage_func(resist, chance, add, damage_mult)
    return function(mons, damage)
        local res_level = 0
        local prop = const.monster_resist_props[resist]
        if prop then
            res_level = mons[prop](mons)
        end

        return damage
            + chance * monster_percent_unresisted(resist, res_level, true)
            * (add + damage_mult * damage)
    end
end

function initialize_ego_damage()
    const.ego_damage_funcs = {
        ["flaming"] = make_damage_func("rF", 1, 0, 0.25),
        ["freezing"] = make_damage_func("rC", 1, 0, 0.25),
        ["electrocution"] = make_damage_func("rElec", 0.25, 14, 0),
        ["venom"] = make_damage_func("rN", 0.5, 3, 0.25),
        ["draining"] = make_damage_func("rN", 0.5, 3, 0.25),
        ["vampirism"] = make_damage_func("rN", 0.6, 0, 0),
        ["holy wrath"] = make_damage_func("rHoly", 1, 0, 0.75),
    }
end

function rated_attack_average_damage(mons, attack, duration_level)
    if not attack.items then
        local damage = you.unarmed_damage_rating()
        damage = (1 + damage) / 2

        local damage_func = const.ego_damage_funcs[you.unarmed_ego()]
        if damage_func then
            damage = damage_func(mons, damage)
        end

        return damage
    end

    local total_damage = 0
    for _, item in ipairs(attack.items) do
        local damage = item.damage_rating()
        damage = (1 + damage) / 2

        if attack.uses_berserk and have_duration("berserk", duration_level) then
            damage = damage + 5.5
        elseif attack.uses_might and have_duration("might", duration_level) then
            damage = damage + 5.5
        end

        if attack.uses_might and have_duration("weak", duration_level) then
            damage = 0.75 * damage
        end

        local damage_func = const.ego_damage_funcs[item.ego()]
        if damage_func then
            damage = damage_func(mons, damage)
        end

        if attack.type == const.attack.melee
                and you.xl() < 18
                and mons:is_real_hydra() then
            local value = hydra_weapon_value(item)
            damage = damage * math.pow(2, value)
        end

        total_damage = total_damage + damage * mons:weapon_accuracy(item)
    end
    return total_damage
end

function evoked_attack_average_damage(mons, attack)
    -- Crawl doesn't have dual evoking, so for simplicity we assume one item.
    local item = attack.items[1]
    local damage = item.evoke_damage
    damage = damage:gsub(".-(%d+)d(%d+).*", "%1 %2")
    -- table.unpack is required since crawl uses Lua 5.4 as of DCSS 0.34.
    local dice, size = table.unpack(split(damage, " "))
    damage = dice * (1 + size) / 2

    local res_prop = const.monster_resist_props[attack.resist]
    if res_prop then
        local res_level = mons[res_prop](mons)
        damage = damage * (1 - attack.resistable
            + attack.resistable
            * monster_percent_unresisted(attack.resist, res_level))
    end

    return damage * mons:evoke_accuracy(item)
end

function player_attack_damage(mons, index, duration_level)
    if not duration_level then
        duration_level = const.duration.active
    end

    local attack = get_attack(index)
    if attack.has_damage_rating then
        return rated_attack_average_damage(mons, attack, duration_level)
    elseif attack.type == const.attack.evoke then
        local damage
        if attack.damage_is_hp then
            if mons:is("paralysed")
                    or mons:status("confused")
                    or mons:status("petrifying")
                    or mons:status("petrified") then
                return 0
            else
                damage = mons:hp()
            end
        else
            damage = evoked_attack_average_damage(mons, attack)
        end

        return damage
    end
end

function unarmed_attack_delay(duration_level)
    if not duration_level then
        duration_level = const.duration.active
    end

    local skill = you.skill("Unarmed Combat")

    if not have_duration("heroism", duration_level)
            and duration_active("heroism") then
        skill = skill - min(27 - skill, 5)
    elseif have_duration("heroism", duration_level)
            and not duration_active("heroism") then
        skill = skill + min(27 - skill, 5)
    end

    local delay = 10 - 10 * skill / 54

    if have_duration("finesse", duration_level) then
        delay = delay / 2
    elseif have_duration("berserk", duration_level) then
        delay = delay * 2 / 3
    elseif have_duration("haste", duration_level) then
        delay = delay * 2 / 3
    end

    if have_duration("slow", duration_level) then
        delay = delay * 3 / 2
    end

    return delay
end

function player_attack_delay_func(index, duration_level)
    if not duration_level then
        duration_level = const.duration.active
    end

    local attack = get_attack(index)
    if attack.items then
        if attack.has_damage_rating then
            local count = 0
            local delay = 0
            for _, weapon in ipairs(attack.items) do
                count = count + 1
                delay = delay + weapon_delay(weapon, duration_level)
            end
            return delay / count
        -- Evocable items.
        else
            local delay = 10

            if have_duration("haste", duration_level) then
                delay = delay * 2 / 3
            end

            if have_duration("slow", duration_level) then
                delay = delay * 3 / 2
            end

            return delay
        end
    else
        return unarmed_attack_delay(duration_level)
    end
end

function player_attack_delay(index, duration_level)
    return turn_memo_args("player_attack_delay",
        function()
            return player_attack_delay_func(index, duration_level)
        end, index, duration_level)
end

function monster_best_player_attack(mons)
    local base_threat = mons:threat()
    local base_damage = mons:player_attack_damage(1) / player_attack_delay(1)
    local best_attack, best_threat
    for i, attack in ipairs(get_attacks()) do
        if not attack.prefer_melee and mons:player_can_attack(i) then
            local damage = player_attack_damage(mons, i,
                    const.duration.available)
                / player_attack_delay(i, const.duration.available)
            local threat = base_threat * base_damage / damage
            if threat < 3 then
                return attack
            elseif not best_threat or threat < best_threat then
                best_attack = attack
                best_threat = threat
            end
        end
    end

    return best_attack
end
------------------------------
-- Branch data and logic

-- Some tables with hardcoded data about branches/gods/portals/monsters:

-- Branch data: branch abbreviation, interlevel travel code, max depth,
-- entrance description, parent branch, min parent branch depth, max parent
-- branch depth, rune name(s).
--
-- This gets loaded into the branch_data table, which is keyed by the branch
-- name. Use the helper functions to access this data: branch_travel(),
-- branch_depth(), parent_branch(), and have_branch_runes().
local branch_data_values = {
    { "D", "D", 15 },
    { "Ossuary", nil, 1, "enter_ossuary" },
    { "Sewer", nil, 1, "enter_sewer" },
    { "Bailey", nil, 1, "enter_bailey" },
    { "IceCv", nil, 1, "enter_ice_cave" },
    { "Volcano", nil, 1, "enter_volcano" },
    { "Bailey", nil, 1, "enter_bailey" },
    { "Gauntlet", nil, 1, "enter_gauntlet" },
    { "Bazaar", nil, 1, "enter_bazaar" },
    { "WizLab", nil, 1, "enter_wizlab" },
    { "Desolation", nil, 1, "enter_desolation" },
    { "Temple", "T", 1, "enter_temple", "D", 4, 7 },
    { "Orc", "O", 2, "enter_orcish_mines", "D", 9, 12 },
    { "Elf", "E", 3, "enter_elven_halls", "Orc", 2, 2 },
    { "Lair", "L", 5, "enter_lair", "D", 8, 11 },
    { "Swamp", "S", 4, "enter_swamp", "Lair", 2, 4, { "decaying" } },
    { "Shoals", "A", 4, "enter_shoals", "Lair", 2, 4, { "barnacled" } },
    { "Snake", "P", 4, "enter_snake_pit", "Lair", 2, 4, { "serpentine" } },
    { "Spider", "N", 4, "enter_spider_nest", "Lair", 2, 4, { "gossamer" } },
    { "Slime", "M", 5, "enter_slime_pits", "Lair", 5, 6, { "slimy" } },
    { "Vaults", "V", 5, "enter_vaults", "D", 13, 14, { "silver" } },
    { "Crypt", "C", 3, "enter_crypt", "Vaults", 3, 4 },
    { "Tomb", "W", 3, "enter_tomb", "Crypt", 3, 3, { "golden" } },
    { "Depths", "U", 4, "enter_depths", "D", 15, 15 },
    { "Zig", nil, 27, "enter_ziggurat", "Depths", 1, 4 },
    { "Zot", "Z", 5, "enter_zot", "Depths", 4, 4 },
    { "Pan", nil, 1, "enter_pandemonium", "Depths", 2, 2,
        { "dark", "demonic", "fiery", "glowing", "magical" } },
    { "Abyss", nil, 7, "enter_abyss", "Depths", 3, 3, { "abyssal" } },
    { "Hell", "H", 1, "enter_hell", "Depths", 1, 4 },
    { "Dis", "I", 7, "enter_dis", "Hell", 1, 1, { "iron" } },
    { "Geh", "G", 7, "enter_gehenna", "Hell", 1, 1, { "obsidian" } },
    { "Coc", "X", 7, "enter_cocytus", "Hell", 1, 1, { "icy" } },
    { "Tar", "Y", 7, "enter_tartarus", "Hell", 1, 1, { "bone" } },
}

hell_branches = { "Coc", "Dis", "Geh", "Tar" }

-- Portal branch, entry description, max timeout in turns, description.
local portal_data_values = {
    { "Ossuary", "sand-covered staircase",
        "The hiss of flowing sand is almost imperceptible now", 800 },
    { "Sewer", "glowing drain", "You hear the drain falling apart", 800 },
    { "Bailey", "flagged portal", "has been lowered almost to the ground",
        800 },
    { "Volcano", "dark tunnel",
        "The sound of falling rocks suddenly begins to subside", 800 },
    { "IceCv", "frozen archway",
        "The crackling of melting ice is subsiding rapidly", 800, "ice cave" },
    { "Gauntlet", "gate leading to a gauntlet",
        "After a thunderous strike, the drumbeats cease", 800 },
    { "Bazaar", "gateway to a bazaar",
        "You hear the last, dying notes of the bell", 1300 },
    { "WizLab", "magical portal",
        "The crackle of the magical portal is almost imperceptible now", 800,
        "wizard's laboratory" },
    { "Desolation", "crumbling gateway",
        "The wind is rapidly growing quiet.", 800 },
    { "Zig", "one-way gateway to a ziggurat", },
}

function initialize_branch_data()
    for _, entry in ipairs(branch_data_values) do
        local branch = entry[1]
        local data = {}
        data["travel"] = entry[2]
        data["depth"] = entry[3]
        data["entrance"] = entry[4]
        data["parent"] = entry[5]
        data["parent_min_depth"] = entry[6]
        data["parent_max_depth"] = entry[7]
        data["runes"] = entry[8]

        -- Update the parent entry depth with that of an entry found in the
        -- parent either if the entry depth is unconfirmed our the found entry
        -- is at a lower depth.
        if c_persist.branch_entries[branch] then
            for level, _ in pairs(c_persist.branch_entries[branch]) do
                local parent, depth = parse_level_range(level)
                if parent == data.parent
                        and (not data.parent_min_depth
                            or data.parent_min_depth ~= data.parent_max_depth
                            or depth < data.parent_min_depth) then
                    data.parent_min_depth = depth
                    data.parent_max_depth = depth
                    break
                end
            end
        end

        branch_data[branch] = data
    end

    for _, entry in ipairs(portal_data_values) do
        local br = entry[1]
        local data = {}
        data["entrance_description"] = entry[2]
        data["final_message"] = entry[3]
        data["timeout"] = entry[4]
        data["description"] = entry[5]
        if not data["description"] then
            data["description"] = br:lower()
        end
        portal_data[br] = data
    end

    early_vaults = make_level_range("Vaults", 1, -1)
    vaults_end = branch_end("Vaults")

    early_zot = make_level_range("Zot", 1, -1)
    zot_end = branch_end("Zot")
end

function branch_travel(branch)
    if not branch_data[branch] then
        error("Unknown branch: " .. tostring(branch))
    end

    return branch_data[branch].travel
end

function branch_depth(branch)
    if not branch_data[branch] then
        error("Unknown branch: " .. tostring(branch))
    end

    return branch_data[branch].depth
end

function branch_entrance(branch)
    if not branch_data[branch] then
        error("Unknown branch: " .. tostring(branch))
    end

    return branch_data[branch].entrance
end

function branch_exit(branch)
    if not branch_data[branch] then
        error("Unknown branch: " .. tostring(branch))
    end

    local result
    if branch_data[branch].entrance then
        -- We want only the first result from gsub().
        result = branch_data[branch].entrance:gsub("enter", "exit", 1)
    elseif branch == "D" then
        result = "exit_dungeon"
    end
    return result
end

function portal_entrance_description(portal)
    if not portal_data[portal] then
        error("Unknown portal: " .. tostring(portal))
    end

    return portal_data[portal].entrance_description
end

function remove_expired_portal(level)
    if not c_persist.portals[level]
            or not c_persist.expiring_portals[level]
            or not c_persist.expiring_portals[level][1] then
        return
    end

    local expiring = c_persist.expiring_portals[level][1]
    for portal, turns_list in pairs(c_persist.portals[level]) do
        if portal == expiring then
            remove_portal(level, portal)
            table.remove(c_persist.expiring_portals[level], 1)
        end
    end
end

function portal_final_message(portal)
    if not portal_data[portal] then
        error("Unknown portal: " .. tostring(portal))
    end

    return portal_data[portal].final_message
end

function record_portal_final_message(level, text)
    if not c_persist.portals[level] then
        return false
    end

    for portal, _ in pairs(c_persist.portals[level]) do
        if text:find(portal_final_message(portal)) then
            if not c_persist.expiring_portals[level] then
                c_persist.expiring_portals[level] = {}
            end

            table.insert(c_persist.expiring_portals[level], portal)
            return true
        end
    end

    return false
end

function portal_timeout(portal)
    if not portal_data[portal] then
        error("Unknown portal: " .. tostring(portal))
    end

    return portal_data[portal].timeout
end

function portal_description(portal)
    if not portal_data[portal] then
        error("Unknown portal: " .. tostring(portal))
    end

    return portal_data[portal].description
end

function parent_branch(branch)
    if not branch_data[branch] then
        error("Unknown branch: " .. tostring(branch))
    end

    return branch_data[branch].parent,
        branch_data[branch].parent_min_depth,
        branch_data[branch].parent_max_depth
end

function branch_runes(branch, item_names)
    if not branch_data[branch] then
        error("Unknown branch: " .. tostring(branch))
    end

    local runes = branch_data[branch].runes
    if runes and item_names then
        local rune_items = {}
        for _, rune in ipairs(runes) do
            table.insert(rune_items, rune .. const.rune_suffix)
        end
        return rune_items
    else
        return runes
    end
end

function branch_exists(branch)
    return not (branch == "Snake" and branch_found("Spider")
        or branch == "Spider" and branch_found("Snake")
        or branch == "Shoals" and branch_found("Swamp")
        or branch == "Swamp" and branch_found("Shoals")
        or not branch_data[branch])
end

function branch_found(branch, min_state)
    if branch == "D" then
        return {"D:0"}
    end

    if not min_state then
        min_state = const.explore.seen
    end

    if not c_persist.branch_entries[branch] then
        return
    end

    for level, state in pairs(c_persist.branch_entries[branch]) do
        if state.feat >= min_state then
            return level
        end
    end
end

function in_branch(branch)
    return where_branch == branch
end

function branch_end(branch)
    return make_level(branch, branch_depth(branch))
end

function at_branch_end(branch)
    if not branch then
        branch = where_branch
    end

    return where_branch == branch and where_depth == branch_depth(branch)
end

function is_hell_branch(branch)
    return util.contains(hell_branches, branch)
end

function in_hell_branch()
    return is_hell_branch(where_branch)
end

function branch_rune_depth(branch)
    if not branch_runes(branch) then
        return
    end

    if branch == "Abyss" then
        return 4
    else
        return branch_depth(branch)
    end
end

function have_branch_runes(branch)
    local runes = branch_runes(branch)
    if not runes then
        return true
    end

    for _, rune in ipairs(runes) do
        if not you.have_rune(rune) then
            return false
        end
    end
    return true
end

function is_portal_branch(branch)
    return portal_data[branch] ~= nil
end

function in_portal()
    return is_portal_branch(where_branch)
end

function portal_allowed(portal)
    return qw.allowed_portals and util.contains(qw.allowed_portals, portal)
end

function record_portal(level, portal, permanent)
    if not c_persist.portals[level] then
        c_persist.portals[level] = {}
    end

    if not c_persist.portals[level][portal] then
        c_persist.portals[level][portal] = {}
    end

    -- This timed portal has already been recorded for this level.
    local len = #c_persist.portals[level][portal]
    if not permanent
            and len > 0
            and c_persist.portals[level][portal][len] ~= const.inf_turns then
        return
    end

    if debug_channel("explore") then
        dsay("Found " .. portal)
    end

    -- Permanent portals go at the beginning, so they'll always be chosen last.
    -- We can't have multiple timed portals of the same type on the same level,
    -- so this scheme puts portals in the correct order. For timed portals,
    -- record the turns to allow prioritizing among timed portals across
    -- levels.
    if permanent then
        table.insert(c_persist.portals[level][portal], 1, const.inf_turns)
    else
        table.insert(c_persist.portals[level][portal], you.turns())
    end

    if portal_allowed(portal) then
        qw.want_goal_update = true
    end
end

function remove_portal(level, portal, silent)
    if not c_persist.portals[level]
            or not c_persist.portals[level][portal]
            or #c_persist.portals[level][portal] == 0 then
        return
    end

    -- This is a list because bazaars can be both permanent and timed and
    -- potentially with both on the same level. We make the list so the timed
    -- portal is at the end, and since we enter timed portals before the
    -- permanent one, we always want to remove from the end.
    table.remove(c_persist.portals[level][portal])
    branch_data[portal].parent = nil
    branch_data[portal].parent_min_depth = nil
    branch_data[portal].parent_max_depth = nil

    if portal_allowed(portal) then
        if not silent then
            say("RIP " .. portal:upper())
        end

        qw.want_goal_update = true
    end
end

-- Expire any timed portals for levels we've fully explored or where they're
-- older than their max timeout.
function update_expired_portals()
    for level, portals in pairs(c_persist.portals) do
        for portal, turns_list in pairs(portals) do
            local timeout = portal_timeout(portal)
            for _, turns in ipairs(turns_list) do
                if where_branch ~= portal
                        and timeout
                        and turns ~= const.inf_turns
                        and you.turns() - turns > timeout then
                    remove_portal(level, portal)
                end
            end
        end
    end
end

function branch_is_temporary(branch)
    return is_portal_branch(branch) or branch == "Pan" or branch == "Abyss"
end

function easy_runes()
    local branches = {"Swamp", "Snake", "Shoals", "Spider"}
    local count = 0
    for _, br in ipairs(branches) do
        if have_branch_runes(br) then
            count = count + 1
        end
    end
    return count
end

function branch_entry_level(branch)
    local parent, min_depth, max_depth = parent_branch(branch)
    if not min_depth or min_depth ~= max_depth then
        return
    end

    return make_level(parent, min_depth)
end
------------------
-- Debug functions

function initialize_debug()
    qw.debug_mode = DEBUG_MODE
    qw.debug_channels = {}
    for _, channel in ipairs(DEBUG_CHANNELS) do
        qw.debug_channels[channel] = true
    end
end

function toggle_debug()
    qw.debug_mode = not qw.debug_mode
    dsay((qw.debug_mode and "Enabling" or "Disabling") .. " debug mode")
end

function debug_channel(channel)
    return qw.debug_mode and qw.debug_channels[channel]
end

function toggle_debug_channel(channel)
    qw.debug_channels[channel] = not qw.debug_channels[channel]
    dsay((qw.debug_channels[channel] and "Enabling " or "Disabling ")
      .. channel .. " debug channel")
end

function disable_all_debug_channels()
    dsay("Disabling all debug channels")
    qw.debug_channels = {}
end

function dsay(x, do_note)
    -- Convert x to string to make debugging easier. We don't do this for say()
    -- and note() so we can catch errors.
    local str
    if type(x) == "table" then
        str = qw.stringify_table(x)
    else
        str = qw.stringify(x)
    end

    str = you.turns() .. " ||| " .. str
    crawl.mpr(str)

    if do_note then
        note(str)
    end
end

function test_radius_iter()
    dsay("Testing 3, 3 with radius 1")
    for pos in radius_iter({ x = 3, y = 3 }, 1) do
        dsay("x: " .. tostring(pos.x) .. ", y: " .. tostring(pos.y))
    end

    dsay("Testing const.origin with radius 3")
    for pos in radius_iter(const.origin, 3) do
        dsay("x: " .. tostring(pos.x) .. ", y: " .. tostring(pos.y))
    end
end

function print_traversal_map(center)
    if not center then
        center = const.origin
    end

    crawl.setopt("msg_condense_repeats = false")

    local map_center = position_sum(qw.map_pos, center)
    say("Traversal map at " .. cell_string_from_map_position(map_center))
    -- This needs to iterate by row then column for display purposes.
    for y = -20, 20 do
        local str = ""
        for x = -20, 20 do
            local pos = position_sum(map_center, { x = x, y = y })
            local traversable = map_is_traversable_at(pos)
            local char
            if positions_equal(pos, qw.map_pos) then
                if traversable == nil then
                    str = str .. "✞"
                else
                    str = str .. (traversable and "@" or "7")
                end
            elseif positions_equal(pos, map_center) then
                if traversable == nil then
                    str = str .. "W"
                else
                    str = str .. (traversable and "&" or "8")
                end
            elseif traversable == nil then
                str = str .. " "
            else
                str = str .. (traversable and "." or "#")
            end
        end
        say(str)
    end

    crawl.setopt("msg_condense_repeats = true")
end

function print_unexcluded_map(center)
    if not center then
        center = const.origin
    end

    crawl.setopt("msg_condense_repeats = false")

    local map_center = position_sum(qw.map_pos, center)
    say("Unexcluded map at " .. cell_string_from_map_position(map_center))
    -- This needs to iterate by row then column for display purposes.
    for y = -20, 20 do
        local str = ""
        for x = -20, 20 do
            local pos = position_sum(map_center, { x = x, y = y })
            local unexcluded = map_is_unexcluded_at(pos)
            local char
            if positions_equal(pos, qw.map_pos) then
                if unexcluded == nil then
                    str = str .. "✞"
                else
                    str = str .. (unexcluded and "@" or "7")
                end
            elseif positions_equal(pos, map_center) then
                if unexcluded == nil then
                    str = str .. "W"
                else
                    str = str .. (unexcluded and "&" or "8")
                end
            elseif unexcluded == nil then
                str = str .. " "
            else
                str = str .. (unexcluded and "." or "#")
            end
        end
        say(str)
    end

    crawl.setopt("msg_condense_repeats = true")
end

function print_adjacent_floor_map(center)
    if not center then
        center = const.origin
    end

    crawl.setopt("msg_condense_repeats = false")

    local map_center = position_sum(qw.map_pos, center)
    say("Adjacent floor map at " .. cell_string_from_map_position(map_center))
    -- This needs to iterate by row then column for display purposes.
    for y = -20, 20 do
        local str = ""
        for x = -20, 20 do
            local pos = position_sum(map_center, { x = x, y = y })
            local floor_count = adjacent_floor_map[pos.x][pos.y]
            local char
            if positions_equal(pos, qw.map_pos) then
                if floor_count == nil then
                    str = str .. "✞"
                else
                    str = str .. (floor_count <= 3 and "@" or "7")
                end
            elseif positions_equal(pos, map_center) then
                if floor_count == nil then
                    str = str .. "W"
                else
                    str = str .. (floor_count <= 3 and "&" or "8")
                end
            elseif floor_count == nil then
                str = str .. " "
            else
                str = str .. floor_count
            end
        end
        say(str)
    end

    crawl.setopt("msg_condense_repeats = true")
end

function print_distance_map(dist_map, center, excluded)
    if not center then
        center = const.origin
    end

    crawl.setopt("msg_condense_repeats = false")

    local map = excluded and dist_map.excluded_map or dist_map.map
    local map_center = position_sum(qw.map_pos, center)
    say("Distance map at " .. cell_string_from_map_position(dist_map.pos)
        .. " from position " .. cell_string_from_map_position(map_center))
    -- This needs to iterate by row then column for display purposes.
    for y = -20, 20 do
        local str = ""
        for x = -20, 20 do
            local pos = position_sum(map_center, { x = x, y = y })
            local dist = map[pos.x][pos.y]
            if positions_equal(pos, qw.map_pos) then
                if dist == nil then
                    str = str .. "✞"
                else
                    str = str .. (dist > 180 and "7" or "@")
                end
            elseif positions_equal(pos, map_center) then
                if dist == nil then
                    str = str .. "W"
                else
                    str = str .. (dist > 180 and "8" or "&")
                end
            else
                if dist == nil then
                    str = str .. " "
                elseif dist > 180 then
                    str = str .. "∞"
                elseif dist > 61 then
                    str = str .. "Ø"
                else
                    str = str .. string.char(string.byte('A') + dist)
                end
            end
        end
        say(str)
    end

    crawl.setopt("msg_condense_repeats = true")
end

function print_distance_maps(center, excluded)
    if not center then
        center = const.origin
    end

    for _, dist_map in pairs(distance_maps) do
        print_distance_map(dist_map, center, excluded)
    end
end

function set_counter()
    crawl.formatted_mpr("Set game counter to what? ", "prompt")
    local res = crawl.c_input_line()
    c_persist.record.counter = tonumber(res)
    note("Game counter set to " .. c_persist.record.counter)
end

function override_goal(goal)
    debug_goal = goal
    update_goal()
end

function get_vars()
    return qw, const
end

function pos_string(pos)
    return tostring(pos.x) .. "," .. tostring(pos.y)
end

function los_pos_string(map_pos)
    return pos_string(position_difference(map_pos, qw.map_pos))
end

function cell_string(cell)
    local str = pos_string(cell.los_pos) .. " ("
    if supdist(cell.los_pos) <= qw.los_radius then
        local mons = monster.get_monster_at(cell.los_pos.x, cell.los_pos.y)
        if mons then
            str = str .. mons:name() .. "; "
        end
    end

    return str .. cell.feat .. ")"
end

function cell_string_from_position(pos)
    return cell_string(cell_from_position(pos))
end

function cell_string_from_map_position(pos)
    return cell_string_from_position(position_difference(pos, qw.map_pos))
end

function monster_string(mons, props)
    if not props then
        props = { move_delay = "move delay", reach_range = "reach",
            is_ranged = "ranged" }
    end

    local vals = {}
    for prop, name in pairs(props) do
        table.insert(vals, name .. ":" .. tostring(mons[prop](mons)))
    end
    return mons:name() .. " (" .. table.concat(vals, "/") .. ") at "
        .. pos_string(mons:pos())
end

function toggle_throttle()
    qw.coroutine_throttle = not qw.coroutine_throttle
    dsay((qw.coroutine_throttle and "Enabling" or "Disabling")
      .. " coroutine throttle")
end

function toggle_delay()
    qw.delayed = not qw.delayed
    dsay((qw.delayed and "Enabling" or "Disabling") .. " action delay")
end

function reset_coroutine()
    qw.update_coroutine = nil
    collectgarbage("collect")
end

function resume_qw()
    qw.abort = false
end

function toggle_single_step()
    qw.single_step = not qw.single_step
    dsay((qw.single_step and "Enabling" or "Disabling")
      .. " single action steps.")
end

function qw.stringify(x)
    local t = type(x)
    if t == "nil" then
        return "nil"
    elseif t == "number" or t == "function" then
        return tostring(x)
    elseif t == "string" then
        return x
    elseif t == "boolean" then
        return x and "true" or "false"
    elseif x.name then
        return item_string(x)
    end
end

function qw.stringify_table(tab, indent_level)
    if not indent_level then
        indent_level = 0
    end

    local spaces = ""
    for i = 1, 2 * indent_level + 1 do
        spaces = spaces .. " "
    end

    if type(tab.pos) == "function" then
        return spaces .. "{ " .. cell_string_from_position(tab:pos()) .. " }"
    end

    local res = spaces .. "{\n"
    for key, val in pairs(tab) do
        res = res .. spaces .. " [" .. qw.stringify(key) .. "] ="
        if type(val) ~= "table" then
            res = res .. " " .. qw.stringify(val) .. ",\n"
        elseif next(val) == nil then -- table is empty
            res = res .. " { },\n"
        else
            res = res .. "\n" .. qw.stringify_table(val, indent_level + 1) .. ",\n"
        end
    end
    res = res .. spaces .. "}"
    return res
end
-------------------------------------
-- Equipment comparisons.

-- We assign a numerical value to all armour/weapon/jewellery, which
-- is used both for autopickup (so it has to work for unIDed items) and
-- for equipment selection. A negative value means we prefer an empty slot.

-- The valuation functions either return a pair of numbers - minimum
-- minimum and maximum potential value - or the current value. Here
-- value should be viewed as utility relative to not wearing anything in
-- that slot. For the current value calculation, we can specify an equipped
-- item and try to simulate not wearing it (for property values).

-- We pick up an item if its max value is greater than our currently equipped
-- item's min value. We swap to an item if it has a greater cur value.

-- if cur, return the current value instead of minmax
-- if it2, pretend we aren't equipping it2
-- if sit = "hydra", assume we are fighting a hydra at lowish XL
--        = "bless", assume we want to bless the weapon with TSO eventually
function equip_value(item, cur, ignore_equip, sit, only_linear)
    if not item then
        return -1, -1
    end

    local slot = equip_slot(item)
    if const.armour_equip_names[slot] then
        return armour_value(item, cur, ignore_equip, only_linear)
    elseif slot == "weapon" then
        return weapon_value(item, cur, ignore_equip, sit, only_linear)
    elseif slot == "amulet" then
        return amulet_value(item, cur, ignore_equip, only_linear)
    elseif slot == "ring" then
        return ring_value(item, cur, ignore_equip, only_linear)
    elseif slot == "gizmo" then
        return gizmo_value(item, ignore_equip, only_linear)
    end

    return -1, -1
end

function equip_set_value(equip, ignore_item)
    if ignore_item then
        new_equip = {}
        local found_equip = false
        for slot, item in equip_set_iter(equip) do
            if item.slot ~= ignore_item.slot then
                if not new_equip[slot] then
                    new_equip[slot] = {}
                end

                table.insert(new_equip[slot], item)
                found_equip = true
            end
        end

        if not found_equip then
            return 0
        end

        equip = new_equip
    end

    local total_value, weapon_delay, weapon_count = 0, 0, 0
    for slot, item in equip_set_iter(equip) do
        local value = 0
        if slot == "weapon" then
            weapon_delay = weapon_delay + weapon_min_delay(item)
            weapon_count = weapon_count + 1
        elseif const.armour_equip_names[slot] then
            value = armour_base_value(item, true)
        elseif slot == "amulet" then
            value = amulet_base_value(item, true)
        elseif slot == "gizmo" then
            value = gizmo_base_value(item)
        end

        if value < 0 then
            return value
        end

        for _, prop in ipairs(const.linear_properties) do
            value = value
                + item_property(prop, item) * linear_property_value(prop)
        end

        total_value = total_value + value
    end

    if weapon_count > 0 then
        weapon_delay = weapon_delay / weapon_count
        local skill = weapon_skill()
        for weapon in equip_set_slot_iter(equip, "weapon") do
            local value = weapon_base_value(weapon, true)
            if value < 0 then
                return value
            end

            value = value + weapon_damage_value(weapon, weapon_delay)

            if weapon.weap_skill ~= skill then
                value = value / 10
            end

            total_value = total_value + value
        end
    end

    local cur_equip = inventory_equip(const.inventory.equipped)
    for _, prop in ipairs(const.nonlinear_properties) do
        local level = 0
        for _, item in equip_set_iter(equip) do
            level = level + item_property(prop, item)
        end

        local player_level = player_property(prop, cur_equip)
        total_value = total_value
            + absolute_property_value(prop, player_level + level)
            - absolute_property_value(prop, player_level)
    end

    return total_value
end

function best_inventory_equip(extra_item)
    local extra_slot = equip_slot(extra_item)
    if extra_item and (not extra_slot or equip_is_dominated(extra_item)) then
        return
    end

    local inventory = inventory_equip(const.inventory.value)
    if not inventory then
        if not extra_item then
            return
        end

        inventory = {}
    end

    local best_equip
    local iter_count = 1
    for equip in equip_combo_iter(inventory, extra_item) do
        equip.value = equip_set_value(equip)

        if debug_channel("items") then
            dsay("Iteration #" .. tostring(iter_count) .. ": "
                .. equip_set_string(equip) .. "; value: "
                .. tostring(equip.value))
        end

        if equip.value > 0
                and (not best_equip or equip.value > best_equip.value) then
            best_equip = equip
        end

        iter_count = iter_count + 1
    end

    if debug_channel("items") then
        if best_equip then
            dsay("Best equip set: " .. equip_set_string(best_equip)
                .. "; value: " .. tostring(best_equip.value))
        else
            dsay("No best equip set found")
        end
    end

    return best_equip
end

function best_equip_from_c_persist()
    if not c_persist.best_equip or not c_persist.best_equip.value then
        return
    end

    local equip = { value = c_persist.best_equip.value }
    c_persist.best_equip.value = nil
    for letter, name in pairs(c_persist.best_equip) do
        local item = get_item(letter)
        if not item or item.name() ~= name then
            return
        end

        local slot = equip_slot(item)
        if not equip[slot] then
            equip[slot] = {}
        end

        table.insert(equip[slot], item)
    end
    c_persist.best_equip.value = equip.value
    return equip
end

function equip_set_value_search(equip, filter, min_value)
    local best_item, best_value
    for slot, item in equip_set_iter(equip) do
        if not filter or filter(item) then
            local value = equip.value - equip_set_value(equip, item)
            if not best_value
                    or min_value and value < best_value
                    or not min_value and value > best_value then
                best_item = item
                best_value = value
            end
        end
    end
    return best_item, best_value
end

function remove_equip_set_item(item, equip)
    local slot = equip_slot(item)
    if not equip[slot] then
        return
    end

    for i, set_item in ipairs(equip[slot]) do
        if equip[slot][i].slot == item.slot then
            if #equip[slot] == 1 then
                equip[slot] = nil
            else
                table.remove(equip[slot], i)
            end

            return
        end
    end
end

function best_equip_set()
    if qw.best_equip then
        return qw.best_equip
    end

    qw.best_equip = best_equip_from_c_persist()
    if qw.best_equip then
        return qw.best_equip
    end

    local equip = best_inventory_equip()
    if not equip then
        c_persist.best_equip = nil
        return
    end

    repeat
        local worst_item, worst_value = equip_set_value_search(equip,
            nil, true)

        if worst_value and worst_value <= 0 then
            if debug_channel("items") then
                dsay("Removing best equip set item " .. worst_item.name()
                    .. " with value " .. tostring(worst_value))
            end

            remove_equip_set_item(worst_item, equip)
            equip.value = equip.value - worst_value
        end
    until not worst_value or worst_value > 0
    qw.best_equip = equip

    if debug_channel("items") then
        dsay("Final best equip set: " .. equip_set_string(qw.best_equip)
            .. "; value: " .. tostring(qw.best_equip.value))
    end

    c_persist.best_equip = {}
    for _, item in equip_set_iter(qw.best_equip) do
        c_persist.best_equip[item_letter(item)] = item.name()
    end
    c_persist.best_equip.value = qw.best_equip.value

    return qw.best_equip
end

-- Is the first item going to be worse than the second item no matter what
-- other properties we have?
function property_dominated(item1, item2)
    local bmin1, bmax1 = equip_value(item1, false, nil, nil, true)
    local bmin2, bmax2 = equip_value(item2, false, nil, nil, true)
    local diff = bmin2 - bmax1
    if diff < 0 then
        return false
    end

    local props1 = property_array(item1)
    local props2 = property_array(item2)
    for i = 1, #props1 do
        if props1[i] > props2[i] then
            diff = diff - (props1[i] - props2[i])
        end
    end
    return diff >= 0
end

function armour_base_value(item, cur)
    local value = 0
    local min_val, max_val = 0, 0

    if current_god_hates_item(item) then
        if cur then
            return -1, -1
        else
            min_val = -10000
        end
    elseif not cur and future_gods_hate_item(item) then
        min_val = -10000
    end

    local name = item.name()
    if item.artefact then
        -- Unrands
        if name:find("hauberk") then
            return -1, -1
        end

        if you.race() ~= "Djinni" and item.name():find("Mad Mage's Maulers") then
            if you.god() ~= "No God" and qw.planned_gods_all_use_mp then
                return -1, -1
            elseif god_uses_mp() then
                if cur then
                    return -1, -1
                else
                    min_val = -10000
                end
            elseif not cur and qw.future_gods_use_mp then
                min_val = -10000
            end

            value = value + 200
        elseif item.name():find("lightning scales") then
            value = value + 100
        end
    end

    local slot = equip_slot(item)
    if slot == "shield" then
        if not want_shield() then
            return -1, -1
        end

        if weapon_skill_uses_dex() then
            -- High Dex builds typically won't have enough Str to mitigate the
            -- tower shield attack delay penalty.
            value = value + (item.encumbrance >= 15 and 50 or 200)
        else
            -- Here 'ac' is actually the base shield rating, which along with
            -- enchantment, shield skill and Str ultimately determines the SH
            -- granted. For Str builds, we're have large amounts of Str and are
            -- fine with training large amounts of shield skill. Hence for
            -- simplicity we only consider the base shield rating. The values
            -- added for buckler/kite/tower shields are 450/750/1050.
            value = value + 270 + 60 * item.ac
        end

        if item.plus then
            value = value + linear_property_value("SH") * item.plus
        end
    else
        local ac_value = linear_property_value("AC")
        value = value + ac_value * expected_armour_multiplier() * item.ac

        if item.plus then
            value = value + ac_value * item.plus
        end
    end

    if slot == "boots" then
        local want_barding = you.race() == "Armataur" or you.race() == "Naga"
        local is_barding = name:find("barding") or name:find("lightning scales")
        if want_barding and not is_barding
                or not want_barding and is_barding then
            return -1, -1
        end
    end

    if slot == "body" then
        if unfitting_armour() then
            value = value - 25 * item.ac
        end

        evp = item.encumbrance
        ap = armour_plan()
        if ap == "heavy" or ap == "large" then
            if evp >= 20 then
                value = value - 100
            elseif name:find("pearl dragon") then
                value = value + 100
            end
        elseif ap == "dodgy" then
            if evp > 11 then
                return -1, -1
            elseif evp > 7 then
                value = value - 100
            end
        else
            if evp > 7 then
                return -1, -1
            elseif evp > 4 then
                value = value - 100
            end
        end
    end

    return min_val + value, max_val + value
end

function armour_value(item, cur, ignore_equip, only_linear)
    local min_val, max_val = armour_base_value(item, cur)

    if cur and min_val < 0 or max_val < 0 then
        return min_val, max_val
    end

    -- Subtype is known and has given us a reasonable value range. We adjust
    -- this range based on the fact that the unknown properties could be good
    -- or bad.
    if not cur and equip_is_valuable_unidentified(item) then
        min_val = min_val + (item.artefact and -400 or -200)
        max_val = max_val + 400
    end

    local res_min, res_max = total_property_value(item, cur, ignore_equip,
        only_linear)
    min_val = min_val + res_min
    max_val = max_val + res_max

    return min_val, max_val
end

function weapons_match_skill(skill)
    for weapon in equipped_slot_iter("weapon") do
        if weapon.weap_skill ~= skill then
            return false
        end
    end

    return true
end

function weapons_have_antimagic()
    for weapon in equipped_slot_iter("weapon") do
        if weapon.ego() == "antimagic" then
            return true
        end
    end

    return false
end

function weapon_base_value(item, cur, sit)
    local value = 1000
    local min_val, max_val = 0, 0

    local hydra_swap = sit == "hydra"
    local weap_skill = weapon_skill()
    -- The evaluating weapon doesn't match our desired skill...
    if item.weap_skill ~= weap_skill
            -- ...and our current weapon already matches our desired skill or
            -- we use UC...
            and (weapons_match_skill(weap_skill)
                or weap_skill == "Unarmed Combat")
            -- ...and we either don't need a hydra swap weapon or the
            -- evaluating weapon isn't a hydra swap weapon for our desired
            -- skill.
            and (not hydra_swap
                or not (item.weap_skill == "Maces & Flails"
                            and weap_skill == "Axes"
                        or item.weap_skill == "Short Blades"
                            and weap_skill == "Long Blades")) then
        return -1, -1
    end

    local name = item.name()
    if sit == "bless" then
        if item.artefact then
            return -1, -1
        elseif not cur and equip_is_valuable_unidentified(item) then
            min_val = min_val - 150
            max_val = max_val + 150
        end

        if item.plus then
            value = value + 30 * item.plus
        end

        value = value + 1200 * item.damage / weapon_min_delay(item)
        return value + min_val, value + max_val
    end

    if current_god_hates_item(item) then
        if cur then
            return -1, -1
        else
            min_val = -10000
        end
    elseif not cur and future_gods_hate_item(item) then
        min_val = -10000
    end

    -- XXX: De-value this on certain levels or give qw better strats while
    -- mesmerised.
    if name:find("obsidian axe") then
        -- This is much less good when it can't make friendly demons.
        if you.mutation("hated by all") or you.god() == "Okawaru" then
            value = value - 200
        elseif qw.future_okawaru then
            min_val = min_val + (cur and 200 or -200)
            max_val = max_val + 200
        else
            value = value + 200
        end
    elseif name:find("consecrated labrys") then
        value = value + 1000
    elseif name:find("storm bow") then
        value = value + 150
    elseif name:find("{damnation}") then
        value = value + 1000
    end

    if item.hands == 2 and not want_two_handed_weapon() then
        return -1, -1
    end

    if hydra_swap then
        local hydra_value = hydra_weapon_value(item)
        if hydra_value < 0 then
            return -1, -1
        elseif hydra_value > 0 then
            value = value + 500
        end
    end

    -- Names are mostly in weapon_brands_verbose[].
    local undead_demon = undead_or_demon_branch_soon()
    local ego = item.ego()
    if ego then
        if ego == "distortion" then
            return -1, -1
        elseif ego == "holy wrath" then
            -- We can never use this.
            if intrinsic_evil() then
                return -1, -1
            end

            if undead_demon then
                min_val = min_val + (cur and 500 or 0)
                max_val = max_val + 500
            -- This will eventaully be good on the Orb run.
            else
                max_val = max_val + 500
            end
        -- Not good against demons or undead, otherwise this is what we want.
        elseif ego == "vampirism" then
            -- It may be good at some point if we go to non undead-demon places
            -- before the Orb. XXX: Determine this from goals and adjust this
            -- value based on the result.
            if undead_demon then
                max_val = max_val + 500
            else
                min_val = min_val + (cur and 500 or 0)
                max_val = max_val + 500
            end
        elseif ego == "speed" then
            -- This is good too
            value = value + 300
        elseif ego == "spectralizing" then
            value = value + 400
        elseif ego == "draining" then
            -- XXX: Same issue as for vampirism above.
            if undead_demon then
                max_val = max_val + 75
            else
                min_val = min_val + (cur and 75 or 0)
                max_val = max_val + 75
            end
        elseif ego == "penetration" then
            value = value + 150
        elseif ego == "heavy" then
            value = value + 100
        elseif ego == "flaming"
                or ego == "freezing"
                or ego == "electrocution" then
            value = value + 75
        elseif ego == "protection" then
            value = value + 50
        elseif ego == "venom" and not undead_demon then
            -- XXX: Same issue as for vampirism above.
            if undead_demon then
                max_val = max_val + 50
            else
                min_val = min_val + (cur and 50 or 0)
                max_val = max_val + 50
            end
        elseif ego == "antimagic" then
            if you.race() ~= "Djinni" then
                local new_mmp = select(2, you.mp())
                -- Swapping to antimagic reduces our max MP by 2/3.
                if not weapons_have_antimagic() then
                    new_mmp = math.floor(select(2, you.mp()) * 1 / 3)
                end
                if not enough_max_mp_for_god(new_mmp, you.god()) then
                    if cur then
                        return -1, -1
                    else
                        min_val = -10000
                    end
                elseif not cur and not future_gods_enough_max_mp(new_mmp) then
                    min_val = -10000
                end
            end

            if you.race() == "Vine Stalker" then
                value = value - 300
            else
                value = value + 75
            end
        elseif ego == "acid" then
            if branch_soon("Slime") then
                if cur then
                    return -1, -1
                else
                    min_val = -10000
                end
            elseif not cur and qw.planning_slime then
                min_val = -10000
            end

            -- The best possible ranged brand aside from possibly holy wrath vs
            -- undead or demons. Keeping this value higher than 500 for now to
            -- make Punk more competitive than all well-enchanted longbows save
            -- those with speed or holy wrath versus demons and undead.
            value = value + 750
        end
    end

    if item.plus then
        value = value + 30 * item.plus
    end

    return min_val + value, max_val + value
end

function weapon_damage_value(item, delay)
    -- We might be delayed by a shield or not yet at min delay, so add a little.
    return 1200 * item.damage / (delay + 1)
end

function weapon_value(item, cur, ignore_equip, sit, only_linear)
    local min_val, max_val = weapon_base_value(item, cur, sit)

    if cur and min_val < 0 or max_val < 0 then
        return min_val, max_val
    end

    local damage_value = weapon_damage_value(item, weapon_min_delay(item))
    min_val = min_val + damage_value
    max_val = max_val + damage_value

    -- The utility from damage is worth much less without training in the skill.
    if item.weap_skill ~= weapon_skill() then
        if min_val > 0 then
            min_val = min_val / 10
        end

        max_val = max_val / 10
    end

    if not cur and equip_is_valuable_unidentified(item) then
        min_val = min_val - 250
        max_val = max_val + 500
    end

    local prop_min, prop_max = total_property_value(item, cur, ignore_equip,
        only_linear)
    return min_val + prop_min, max_val + prop_max
end

function amulet_base_value(item, cur)
    local name = item.name()
    if name:find("macabre finger necklace") then
        return -1, -1
    end

    local min_val, max_val = 0, 0
    if current_god_hates_item(item) then
        if cur then
            return -1, -1
        else
            min_val = -10000
        end
    elseif not cur and future_gods_hate_item(item) then
        min_val = -10000
    end

    if name:find("of the Air.*Inacc") then
        min_val = min_val - 200
        max_val = max_val - 200
    end

    return min_val, max_val
end

function amulet_value(item, cur, ignore_equip, only_linear)
    local min_val, max_val = amulet_base_value(item, cur)

    if cur and min_val < 0 or max_val < 0 then
        return min_val, max_val
    end

    if not cur and equip_is_valuable_unidentified(item) then
        min_val = min_val - 250
        max_val = max_val + 1000
    end

    local prop_min, prop_max = total_property_value(item, cur, ignore_equip,
        only_linear)
    return min_val + prop_min, max_val + prop_max
end

function ring_value(item, cur, ignore_equip, only_linear)
    local min_val, max_val = 0, 0

    if not cur and equip_is_valuable_unidentified(item) then
        min_val = min_val - 250
        max_val = max_val + 500
    end

    local prop_min, prop_max= total_property_value(item, cur, ignore_equip,
        only_linear)
    return min_val + prop_min, max_val + prop_max
end

function gizmo_base_value(item)
    local value = 0
    local ego = item.ego()
    if ego == "Gadgeteer" then
        value = 20
    elseif ego == "AutoDazzle" then
        value = 100
    -- This gets additional value added from its AC property.
    elseif ego == "RevParry" then
        value = 20
    end
    return value
end

function gizmo_value(item, ignore_equip, only_linear)
    return gizmo_base_value(item)
        + total_property_value(item, true, ignore_equip, only_linear)
end

-- Maybe this should check property_dominated too?
function weapon_is_sit_dominated(item, sit)
    local max_val = select(2, weapon_value(item, false, nil, sit))
    if max_val < 0 then
        return true
    end

    for weapon in inventory_slot_iter("weapon") do
        if weapon.slot ~= item.slot
                    and (weapon.hands == 1 or want_two_handed_weapon())
                    and select(2, weapon_value(weapon, false, nil, sit))
                        >= max_val then
            return true
        end
    end

    return false
end

function equip_is_dominated(item)
    local slot = equip_slot(item)
    if you.race() ~= "Coglin"
                and slot == "weapon"
                and you.xl() < 18
                and not weapon_is_sit_dominated(item, "hydra")
            or slot == "weapon"
                and (you.god() == "the Shining One"
                        and not you.one_time_ability_used()
                    or qw.future_tso)
                and not weapon_is_sit_dominated(item, "bless")
            or slot == "gizmo" then
        return false
    end

    local min_val, max_val = equip_value(item)
    if max_val < 0 then
        return true
    end

    local slots_free = slot_max_items(slot)
    for item2 in inventory_slot_iter(slot) do
        if item2.slot ~= item.slot
                and not (want_shield()
                    and weapon_allows_shield(item)
                    and not weapon_allows_shield(item2)) then
            local min_val2, max_val2 = equip_value(item2)
            if min_val2 >= max_val
                    or min_val2 >= min_val
                        and max_val2 >= max_val
                        and property_dominated(item, item2) then
                slots_free = slots_free - 1

                if slots_free == 0 then
                    return true
                end
            end
        end
    end

    return false
end

function best_acquirement_index(acq_items)
    local best_index, gold_index
    local best_equip = best_equip_set()
    for i, item in ipairs(acq_items) do
        local equip = best_inventory_equip(item)
        if equip and (not best_equip or equip.value > best_equip.value) then
            best_equip = equip
            best_index = i
        end

        if item.class(true) == "gold" then
            gold_index = i
        end
    end

    if best_index then
        return best_index
    elseif gold_index then
        return gold_index
    end
end
-------------------------------------
-- Equipment property evaluation.

-- Properties that don't have a linear progression of value at different
-- levels. The Str/Dex/Int in nonlinear_property can only recieve negative
-- utility, which happens when they are reduced to dangerous levels.
const.nonlinear_properties = { "Str", "Dex", "Int", "rF", "rC", "rElec",
    "rPois", "rN", "Will", "rCorr", "SInv", "Fly", "Faith", "Spirit",
    "Acrobat", "Reflect", "RMsl", "Clar", "-Tele", "Ponderous", "Harm",
    "^Fragile", "^Drain", "^Contam" }

const.no_swap_properties = { "^Fragile", "^Drain", "^Contam" }


-- These properties always provide the same benefit (or detriment) with each
-- point of the property.
const.linear_properties = { "Str", "Dex", "Slay", "AC", "EV", "SH", "Regen",
    "*Slow", "*Corrode", "*Tele", "*Rage" }

const.property_max_levels = {}
for _, prop in ipairs(const.nonlinear_properties) do
    local max_level
    if prop == "rF" or prop == "rC" or prop == "rN" then
        max_level = 3
    elseif not (prop == "Str"
            or prop == "Dex"
            or prop == "Int"
            or prop == "Will") then
        max_level = 1
    end
    const.property_max_levels[prop] = max_level
end

-- Returns the amount of an artprop granted by an item.
function item_property(prop, item)
    if not item then
        return 0
    end

    if item.artefact and item.artprops and item.artprops[prop] then
        return item.artprops[prop]
    else
        local name = item.name()
        local ego = item.ego()
        local subtype = item.subtype()
        if prop == "rF" then
            if name:find("fire dragon") then
                return 2
            elseif ego == "fire resistance"
                    or ego == "resistance"
                    or subtype == "ring of protection from fire"
                    or name:find("golden dragon")
                    or subtype == "ring of fire" then
                return 1
            elseif name:find("ice dragon") or subtype == "ring of ice" then
                return -1
            else
                return 0
            end
        elseif prop == "rC" then
            if name:find("ice dragon") then
                return 2
            elseif ego == "cold resistance" or ego == "resistance"
                     or subtype == "ring of protection from cold"
                     or name:find("golden dragon")
                     or subtype == "ring of ice" then
                return 1
            elseif name:find("fire dragon") or subtype == "ring of fire" then
                return -1
            else
                return 0
            end
        elseif prop == "rElec" then
            return name:find("storm dragon") and 1 or 0
        elseif prop == "rPois" then
            return (ego == "poison resistance"
                or subtype == "ring of poison resistance"
                or name:find("swamp dragon")
                or name:find("golden dragon")) and 1 or 0
        elseif prop == "rN" then
            return (ego == "positive energy"
                or subtype == "ring of positive energy"
                or name:find("pearl dragon")) and 1 or 0
        elseif prop == "Will" then
            return (ego == "willpower"
                or subtype == "ring of willpower"
                or name:find("quicksilver dragon")) and 1 or 0
        elseif prop == "rCorr" then
            return (subtype == "ring of resist corrosion"
                or name:find("acid dragon")) and 1 or 0
        elseif prop == "SInv" then
            return (ego == "see invisible"
                or subtype == "ring of see invisible") and 1 or 0
        elseif prop == "Fly" then
            return ego == "flying" and 1 or 0
        elseif prop == "Faith" then
            return subtype == "amulet of faith" and 1 or 0
        elseif prop == "Spirit" then
            return (ego == "spirit shield"
                    or subtype == "amulet of guardian spirit") and 1 or 0
        elseif prop == "Regen" then
             return (name:find("troll leather")
                     or subtype == "amulet of regeneration") and 1 or 0
        elseif prop == "Acrobat" then
             return subtype == "amulet of the acrobat" and 1 or 0
        elseif prop == "Reflect" then
             return (ego == "reflection" or subtype == "amulet of reflection")
                 and 1 or 0
        elseif prop == "*Dream" then
             return name:find("dreamshard necklace") and 1 or 0
        elseif prop == "RMsl" then
             return ego == "repulsion" and 1 or 0
        elseif prop == "Ponderous" then
             return ego == "ponderousness" and 1 or 0
        elseif prop == "Harm" then
             return ego == "harm" and 1 or 0
        elseif prop == "Str" then
            if subtype == "ring of strength" then
                return item.plus or 0
            elseif ego == "strength" then
                return 3
            end
        elseif prop == "Dex" then
            if subtype == "ring of dexterity" then
                return item.plus or 0
            elseif ego == "dexterity" then
                return 3
            end
        elseif prop == "Int" then
            if subtype == "ring of intelligence" then
                return item.plus or 0
            elseif ego == "intelligence" then
                return 3
            end
        elseif prop == "Slay" then
            return subtype == "ring of slaying" and item.plus or 0
        elseif prop == "AC" then
            if subtype == "ring of protection" then
                return item.plus or 0
            -- Wrong for weapons, but we scale things differently for weapons.
            elseif ego == "protection" then
                return 3
            elseif ego == "RevParry" then
                return 5
            end
        elseif prop == "EV" then
            return subtype == "ring of evasion"  and item.plus or 0
        elseif prop == "SH" then
            return subtype == "amulet of reflection" and 5 or 0
        end
    end

    return 0
end

-- The current utility of having a given level of an artprop.
function absolute_property_value(prop, level)
    if prop == "Str" or prop == "Int" or prop == "Dex" then
        if level > 4 then
            -- Handled by linear_property_value()
            return 0
        elseif level > 2 then
            return -100
        elseif level > 0 then
            return -250
        else
            return -10000
        end
    end

    if level == 0 then
        return 0
    end

    if branch_soon("Slime")
            and (prop == "rF"
                or prop == "rElec"
                or prop == "rPois"
                or prop == "rN"
                or prop == "SInv") then
        return 0
    end

    if prop == "rF" or prop == "rC" then
        local value
        -- The value of negative levels is a bit worse than the corresponding
        -- value of the corresponding positive level. This way we'll not value
        -- items that e.g. take us up one level of rC+ yet also down one level
        -- of rF- when we're at rF0 or less.
        if level <= -3 then
            value = -275
        elseif level == -2 then
            value = -225
        elseif level == -1 then
            value = -150
        elseif level == 1 then
            value = 125
        elseif level == 2 then
            value = 200
        else
            value = 250
        end

        if prop == "rF" and (branch_soon("Zot") or branch_soon("Geh")) then
            value = value * 2.5
        elseif prop == "rC" then
            if branch_soon("Coc") then
                value = value * 2.5
            elseif branch_soon("Slime") then
                value = value * 1.5
            end
        end

        return value
    elseif prop == "rElec" then
        return 75
    elseif prop == "rPois" then
        return easy_runes() < 2 and 225 or 75
    elseif prop == "rN" then
        return 25 * min(level, 3)
    elseif prop == "Will" then
        local branch_factor = branch_soon("Vaults") and 1.5 or 1
        return min(100 * branch_factor * level, 300 * branch_factor)
    elseif prop == "rCorr" then
        return branch_soon("Slime") and 1200 or 50
    elseif prop == "SInv" then
        return 200
    elseif prop == "Fly" then
        return 200
    elseif prop == "Faith" then
        -- We don't use invocations enough for these gods to care about Faith.
        if you.god() == "Cheibriados"
                or you.god() == "Beogh"
                or you.god() == "Qazlal"
                or you.god() == "Hepliaklqana" then
        -- These gods gain little from Faith.
        elseif you.god() == "Ru" or you.god() == "Xom" then
            return 0
        -- Otherwise, we like Faith a lot.
        else
            return 1000
        end
    elseif prop == "Spirit" then
        if you.race() == "Djinni" then
            return 0
        else
            return god_uses_mp() and -150 or 100
        end
    elseif prop == "Acrobat" then
        return 100
    elseif prop == "Reflect" then
        return 20
    elseif prop == "RMsl" then
        return 200
    elseif prop == "*Dream" then
        return 100
    elseif prop == "Clar" then
        return you.race() == "Mummy" and 100 or 20
    elseif prop == "Rampage" then
        return using_ranged_weapon() and -50 or 20
    -- Begin properties we always assign a nonpositive value.
    elseif prop == "Harm" then
        return -500
    elseif prop == "Ponderous" then
        return -300
    elseif prop == "-Tele" then
        return you.race() == "Formicid" and 0 or -10000
    end

    return 0
end

function max_property_value(prop, level)
    if level <= 0 then
        return 0
    end

    local ires = intrinsic_property(prop)
    if prop == "rF" or prop == "rC" then
        local value
        if level == 1 then
            value = 125
        elseif level == 2 then
            value = 200
        elseif level == 3 then
            value = 250
        end

        if prop == "rF" then
            value = value * 2.5
        elseif prop == "rC" then
            if qw.planning_cocytus then
                value = value * 2.5
            elseif qw.planning_slime then
                value = value * 1.5
            end
        end
        return value
    elseif prop == "rElec" then
        return ires < 1 and 75 or 0
    elseif prop == "rPois" then
        return ires < 1 and (easy_runes() < 2 and 225 or 75) or 0
    elseif prop == "rN" then
        return ires < 3 and 25 * level or 0
    elseif prop == "Will" then
        local branch_factor = qw.planning_vaults and 1.5 or 1
        return min(100 * branch_factor * level, 300 * branch_factor)
    elseif prop == "rCorr" then
        return ires < 1 and (qw.planning_slime and 1200 or 50) or 0
    elseif prop == "SInv" then
        return ires < 1 and 200 or 0
    elseif prop == "Fly" then
        return ires < 1 and 200 or 0
    elseif prop == "Faith" then
        if you.god() == "Cheibriados"
                or you.god() == "Beogh"
                or you.god() == "Qazlal"
                or you.god() == "Hepliaklqana" then
            return -10000
        elseif you.god() == "Ru" or you.god() == "Xom" then
            return 0
        else
            return 1000
        end
    elseif prop == "Spirit" then
        if ires >= 1
                or you.race() == "Djinni"
                or qw.planned_gods_all_use_mp then
            return 0
        else
            return 100
        end
    elseif prop == "Acrobat" then
        return 100
    elseif prop == "Reflect" then
        return 20
    elseif prop == "RMsl" then
        return 100
    elseif prop == "*Dream" then
        return 200
    elseif prop == "Clar" then
        return you.race() == "Mummy" and 100 or 20
    elseif prop == "Rampage" then
        return using_range_weapon() and 0 or 20
    elseif prop == "Harm" then
        return -500
    elseif prop == "Ponderous" then
        return -300
    elseif prop == "-Tele" then
        return you.race() == "Formicid" and 0 or -10000
    end

    return 0
end

function min_property_value(prop, level)
    if level < 0 then
        if prop == "rF" then
            return -450
        elseif prop == "rC" then
            if qw.planning_cocytus then
                return -450
            elseif qw.planning_slime then
                return -225
            end

            return -150
        elseif prop == "Will" then
            return -75 * level
        end
    elseif level > 0 then
        -- This can only have its effect once, so we want to carry around our
        -- best backup amulet.
        if prop == "*Dream" then
            return -10000
        -- Begin properties that are always bad.
        elseif prop == "Harm" then
            return -500
        elseif prop == "Ponderous" then
            return -300
        elseif prop == "-Tele" then
            return you.race() == "Formicid" and 0 or -10000
        end
    end

    return 0
end

function property_value(prop, item, cur, ignore_equip)
    local item_val = item_property(prop, item)
    if item_val == 0 then
        return 0, 0
    end

    if util.contains(const.no_swap_properties, prop) then
        local bad_for_hydra = item
            and equip_slot(item) == "weapon"
            and you.xl() < 18
            and hydra_weapon_value(item) < 0
        return bad_for_hydra and -500 or 0, 0
    end

    if cur then
        if not ignore_equip and item.equipped then
            local slot = equip_slot(item)
            ignore_equip = { [slot] = { item } }
        end

        local player_val = player_property(prop, ignore_equip)
        local diff = absolute_property_value(prop, player_val + item_val)
            - absolute_property_value(prop, player_val)
        return diff, diff
    else
        return min_property_value(prop, item_val),
            max_property_value(prop, item_val)
    end
end

function weapon_skill_uses_dex()
    local skill = weapon_skill()
    return skill == "Long Blades"
        or skill == "Short Blades"
        or skill == "Ranged Weapons"
end

function linear_property_value(prop)
    local dex_weapon = weapon_skill_uses_dex()
    if prop == "Regen" then
        return 200
    elseif prop == "Slay" or prop == "AC" or prop == "EV" then
        return 50
    elseif prop == "SH" then
        return 40
    elseif prop == "Str" then
        return dex_weapon and 10 or 35
    elseif prop == "Dex" then
        return dex_weapon and 55 or 15
    -- Begin negative properties.
    elseif prop == "*Tele" then
        return you.race() == "Formicid" and 0 or -300
    elseif prop == "*Rage" then
        return (intrinsic_undead() or you.race() == "Formicid")
            and 0 or -300
    elseif prop == "*Slow" then
        return you.race() == "Formicid" and 0 or -100
    elseif prop == "*Corrode" then
        return -100
    end

    return 0
end

function total_property_value(item, cur, ignore_equip, only_linear)
    local value = 0
    for _, prop in ipairs(const.linear_properties) do
        value = value + item_property(prop, item) * linear_property_value(prop)
    end

    if only_linear then
        return value, value
    end

    local min_value, max_value = value, value
    for _, prop in ipairs(const.nonlinear_properties) do
        local prop_min, prop_max = property_value(prop, item, cur,
            ignore_equip)
        min_value = min_value + prop_min
        max_value = max_value + prop_max
    end

    return min_value, max_value
end

function property_array(item)
    local array = {}
    for _, prop in ipairs(const.nonlinear_properties) do
        local min_value, max_value = property_value(prop, item)
        table.insert(array, max_value > 0 and max_value or min_value)
    end
    return array
end
-------------------------------------
-- General equipment manipulation.

const.acquire = { scroll = 1, okawaru_weapon = 2, okawaru_armour = 3,
    gizmo = 4 }

-- A table mapping of armour slots. Used for iteration and to map simple slot
-- names to the full name needed by the items library.
const.armour_slots = { "shield", "body", "cloak", "helmet", "gloves", "boots" }
const.armour_equip_names = { shield="Shield", body="Body Armour", cloak="Cloak",
    helmet="Helmet", gloves="Gloves", boots="Boots" }


const.all_slots = { "weapon", "shield", "body", "helmet", "cloak", "gloves",
    "boots", "amulet", "ring", "gizmo" }
const.all_equip_names = { weapon="Weapon", shield="Shield", body="Body Armour", cloak="Cloak",
    helmet="Helmet", gloves="Gloves", boots="Boots", amulet="Amulet", gizmo="Gizmo" }

const.upgrade_slots = { "body", "helmet", "cloak", "gloves", "boots", "amulet",
    "ring" }

const.inventory = { "all", "value", "equipped" }

const.missile_delays = { dart=10, boomerang=13, javelin=15, ["large rock"]=20 }

function get_slot_item_func(slot, allow_melded)
    local slot_name = const.all_equip_names[slot]
    if not slot_name then
        return
    end

    local item = items.equipped_at(slot_name)
    if not item
            or item.is_melded and not allow_melded
            or equip_slot(item) ~= slot then
        return
    end

    return item
end

function get_slot_item(slot, allow_melded)
    return turn_memo_args("get_slot_item",
        function() return get_slot_item_func(slot, allow_melded) end,
        slot, allow_melded)
end

function get_weapon(allow_melded)
    return get_slot_item("weapon", allow_melded)
end

function get_shield(allow_melded)
    return get_slot_item("shield", allow_melded)
end

function equip_slot(item)
    if not item then
        return
    end

    local class = item.class(true)
    if class == "weapon" then
        return "weapon"
    elseif class == "armour" then
        return item.subtype()
    elseif class == "jewellery" then
        local sub = item.subtype()
        if sub and sub:find("amulet")
               or not sub and item.name():find("amulet") then
            return "amulet"
        else
            return "ring" -- not the actual slot name
        end
    elseif class == "gizmo" then
        return "gizmo"
    end
end

function want_ranged_weapon()
    return turn_memo("want_ranged_weapon",
        function()
            return weapon_skill() == "Ranged Weapons"
        end)
end

function using_ranged_weapon(allow_melded)
    local weapon = get_weapon(allow_melded)
    return weapon and weapon.is_ranged
end

function weapon_allows_shield(weapon)
    return weapon.hands == 1
        or you.race() == "Formicid" and not weapon.subtype():find("giant.* club")
end

function using_two_handed_weapon(allow_melded)
    local weapon = get_weapon(allow_melded)
    return weapon and weapon.hands == 2
end

function using_two_one_handed_weapons(allow_melded)
    return turn_memo_args("using_two_one_handed_weapons",
        function()
            local one_handers = 0
            for weapon in equipped_slot_iter("weapon", allow_melded) do
                if weapon.hands == 1 then
                    one_handers = one_handers + 1
                end

                if one_handers > 1 then
                    return true
                end
            end

            return false
        end, allow_melded)
end

function using_cleave(allow_melded)
    return turn_memo_args("using_cleave",
        function()
            for weapon in equipped_slot_iter("weapon", allow_melded) do
                if weapon.weap_skill == "Axes" then
                    return true
                end
            end
        end, allow_melded)
end

-- Would we ever want to use a two-handed weapon? This returns true when we
-- prefer 1h weapons if we haven't yet found a shield.
function want_two_handed_weapon()
    local sp = you.race()
    if sp == "Felid" or sp == "Coglin" then
        return false
    -- Formicids always use two-handed weapons since they can use them with shields.
    elseif sp == "Formicid" then
        return true
    end

    return want_ranged_weapon() or not (get_shield(true) and qw.shield_crazy)
end

-- Would we ever want a shield?
function want_shield()
    local sp = you.race()
    if sp == "Felid" then
        return false
    elseif sp == "Coglin" then
        return not using_two_one_handed_weapons(true)
    end

    return true
end

function player_reach_range()
    return turn_memo("player_reach_range",
        function()
            local range = 1
            for weapon in equipped_slot_iter("weapon") do
                if weapon.reach_range > range then
                    range = weapon.reach_range
                end
            end

            return range
        end)
end

function weapon_min_delay(weapon)
    local max_delay
    if weapon.delay then
        max_delay = weapon.delay
    elseif weapon.class(true) == "missile" then
        max_delay = const.missile_delays[weapon.subtype()]
    end

    -- The maxes used in this function are used to cover cases like Dark Maul
    -- and Sniper, which have high base delays that can't reach the usual min
    -- delays.
    if contains_string_in(weapon.subtype(), { "crossbow", "arbalest", "cannon" }) then
        return max(10, max_delay - 13.5)
    end

    if weapon.weap_skill == "Short Blades" then
        return 5
    end

    if contains_string_in(weapon.subtype(), { "demon whip", "scourge" }) then
        return 5
    end

    if contains_string_in(weapon.subtype(),
            { "demon blade", "eudemon blade", "trishula", "dire flail" }) then
        return 6
    end

    return max(7, max_delay - 13.5)
end

function weapon_delay(weapon, duration_level)
    if not durations then
        durations = {}
    end

    local skill = you.skill(weapon.weap_skill)
    if not have_duration("heroism", duration_level)
            and duration_active("heroism") then
        skill = skill - min(27 - skill, 5)
    elseif have_duration("heroism", duration_level)
            and not duration_active("heroism") then
        skill = skill + min(27 - skill, 5)
    end

    local delay
    if weapon.delay then
        delay = weapon.delay
    elseif weapon.class(true) == "missile" then
        delay = const.missile_delays[weapon.subtype()]
    end

    delay = max(weapon_min_delay(weapon), delay - skill / 2)

    local ego = weapon:ego()
    if ego == "speed" then
        delay = delay * 2 / 3
    elseif ego == "heavy" then
        delay = delay * 1.5
    end

    if have_duration("finesse", duration_level) then
        delay = delay / 2
    elseif not weapon.is_ranged
            and not weapon.class(true) == "missile"
            and have_duration("berserk", duration_level) then
        delay = delay * 2 / 3
    elseif have_duration("haste", duration_level) then
        delay = delay * 2 / 3
    end

    if have_duration("slow", duration_level) then
        delay = delay * 3 / 2
    end

    return delay
end

function min_delay_skill()
    local max_level
    for weapon in equipped_slot_iter("weapon") do
        local level = min(27, 2 * (weapon.delay - weapon_min_delay(weapon)))
        if not max_level or level > max_level then
            max_level = level
        end
    end

    if max_level then
        return max_level
    -- Unarmed combat
    else
        return 27
    end
end

function at_min_delay()
    return you.base_skill(weapon_skill()) >= min_delay_skill()
end

function armour_evp()
    local armour = get_slot_item("body", true)
    if armour then
        return armour.encumbrance
    else
        return 0
    end
end

function base_ac()
    local ac = 0
    for slot, item in equipped_slots_iter(const.armour_slots, true) do
        if slot ~= "shield" then
            ac = ac + item.ac
        end
    end
    return ac
end

function item_is_unswappable(item)
    for _, prop in ipairs(const.no_swap_properties) do
        if item_property(prop, item) > 0 then
            return true
        end
    end

    return item.ego() == "distortion" and you.god() ~= "Lugonu"
end

function can_swap_item(item, upgrade)
    if not item then
        return true
    end

    if item.is_melded
            or item.name():find("obsidian axe") and you.status("mesmerised")
            or not upgrade and item_is_unswappable(item) then
        return false
    end

    local feat = view.feature_at(0, 0)
    if you.flying()
            and (feat == "deep_water" and not intrinsic_amphibious()
                or feat == "lava")
            and player_property("Fly",
                { [equip_slot(item)] = { item } }) == 0 then
        return false
    end

    return true
end

function equip_set_string(equip)
    local item_letters = {}
    local item_counts = {}
    local slots = {}
    for slot, item in equip_set_iter(equip) do
        if item_counts[slot] then
            item_counts[slot] = item_counts[slot] + 1
        else
            item_counts[slot] = 1
        end

        table.insert(slots, slot)
        table.insert(item_letters, item.slot and item_letter(item) or "?")
        table.insert(item_counts, tostring(item_counts[slot]))
    end

    local entries = {}
    for i, slot in ipairs(slots) do
        local max_items = slot_max_items(slot)
        table.insert(entries, slot .. (max_items > 1 and item_counts[i] or "")
            .. ":" .. item_letters[i])
    end

    return "(" .. table.concat(entries, ", ") .. ")"
end

function equip_set_iter(equip, slots, item_only)
    if not slots then
        slots = const.all_slots
    end

    local slot_num = 1
    local slot = slots[slot_num]
    local slot_ind = 1
    return function()
        if not equip then
            return
        end

        while slot_num <= #slots do
            local slot_items = equip[slot]
            if slot_items and slot_ind <= #slot_items then
                local item = equip[slot][slot_ind]
                slot_ind = slot_ind + 1

                if item_only then
                    return item
                else
                    return slot, item
                end
            else
                slot_num = slot_num + 1
                slot = slots[slot_num]
                slot_ind = 1
            end
        end

        return
    end
end

function equip_set_slot_iter(equip, slot)
    return equip_set_iter(equip, { slot }, true)
end

function inventory_equip_func(inventory_type, ignore_melding)
    local equip = {}
    local found_equip = false
    for _, item in ipairs(items.inventory()) do
        local slot = equip_slot(item)
        if slot and (not item.is_useless or inventory_type == const.inventory.equipped)
                and (ignore_melding or not item.is_melded)
                and (inventory_type ~= const.inventory.equipped
                    or item.equipped)
                and (inventory_type ~= const.inventory.value
                    or slot == "gizmo"
                    or select(2, equip_value(item)) > 0) then
            if not equip[slot] then
                equip[slot] = {}
            end

            found_equip = true
            table.insert(equip[slot], item)
        end
    end
    if found_equip then
        return equip
    end
end

function inventory_equip(inventory_type, ignore_melding)
    return turn_memo_args("inventory_equip",
        function()
            return inventory_equip_func(inventory_type, ignore_melding)
        end, inventory_type, ignore_melding)
end

function inventory_slots_iter(slots, ignore_melding)
    return equip_set_iter(inventory_equip(const.inventory.all, ignore_melding),
        slots)
end

function inventory_slot_iter(slot, ignore_melding)
    return equip_set_slot_iter(inventory_equip(const.inventory.all,
        ignore_melding), slot)
end

function equipped_slots_iter(slots, ignore_melding)
    return equip_set_iter(inventory_equip(const.inventory.equipped,
        ignore_melding), slots)
end

function equipped_slot_iter(slot, ignore_melding)
    return equip_set_slot_iter(inventory_equip(const.inventory.equipped,
        ignore_melding), slot)
end

util.defclass("EquipmentCombinationIterator")

function EquipmentCombinationIterator:new(inventory, extra_item)
    local iter = {}
    setmetatable(iter, self)

    iter.inventory = inventory

    if extra_item then
        iter.extra_item = extra_item

        -- We work off a copy so we can add our extra item without affecting
        -- our memoized data.
        iter.inventory = util.copy_table(iter.inventory)

        local slot = equip_slot(extra_item)
        if not iter.inventory[slot] then
            iter.inventory[slot] = {}
        end

        table.insert(iter.inventory[slot], extra_item)
    end

    iter.inventory_slots = {}
    iter.slot_max_items = {}
    iter.active_slots = {}
    iter.seen_slots = {}
    for _, slot in ipairs(const.all_slots) do
        if iter.inventory[slot] then
            iter.slot_max_items[slot] = slot_max_items(slot)
            iter.seen_slots[slot] = true
            iter.active_slots[slot] = true
            table.insert(iter.inventory_slots, slot)
        end
    end

    iter.first_iteration = true
    iter.equip_indices = {}
    for _, slot in ipairs(iter.inventory_slots) do
        iter.equip_indices[slot] = {}
        iter:reset_equip_indices(slot, 1)
    end

    if debug_channel("items") then
        local inv_counts = {}
        for _, slot in ipairs(iter.inventory_slots) do
            table.insert(inv_counts, slot .. ":"
                .. tostring(#iter.inventory[slot]))
        end
        dsay("Item counts for slots: " .. table.concat(inv_counts, ", "))

        if extra_item then
            dsay("Extra item: " .. qw.stringify(extra_item))
        end
    end

    return iter
end

function EquipmentCombinationIterator:set_equip_index(slot, slot_ind, item_ind)
    local inv = self.inventory[slot]
    local indices = self.equip_indices[slot]
    if slot == "weapon" then
        if self.seen_slots["shield"]
                and slot_ind == 1
                and weapon_allows_shield(inv[item_ind]) then
            self.active_slots["shield"] = true
        elseif not weapon_allows_shield(inv[item_ind]) or slot_ind == 2 then
            self.active_slots["shield"] = false
        end
    end

    if inv[item_ind] == self.extra_item then
        self.extra_used = true
    elseif indices[slot_ind] and inv[indices[slot_ind]] == self.extra_item then
        self.extra_used = false
    end

    indices[slot_ind] = item_ind
end

function EquipmentCombinationIterator:reset_equip_indices(slot, slot_ind)
    local inv = self.inventory[slot]
    local num_items = #inv
    local max_items = min(num_items, self.slot_max_items[slot])

    -- There are no remaining slots to reset.
    if slot_ind > max_items then
        return true
    end

    local item_ind = 1
    local indices = self.equip_indices[slot]
    -- The first slot is always reset to the first item, since when it's reset,
    -- we're resetting all slots to the initial configuration. For subsequent
    -- slots, we reset them to the first item after the one used by the
    -- previous slot.
    if slot_ind > 1 then
        item_ind = indices[slot_ind - 1] + 1
    end

    -- We have no more unused inventory items to put in slots.
    if item_ind > num_items then
        return false
    end

    for j = 0, max_items - slot_ind do
        self:set_equip_index(slot, slot_ind + j, item_ind + j)
    end

    return true
end

function EquipmentCombinationIterator:iterate_equip_slot(slot)
    if self.first_iteration then
        self.first_iteration = false
        return true
    end

    local indices = self.equip_indices[slot]
    local inv = self.inventory[slot]
    local num_items = #inv
    local max_items = min(num_items, self.slot_max_items[slot])
    for i = max_items, 1, -1 do
        if indices[i] < num_items - (max_items - i) then
            self:set_equip_index(slot, i, indices[i] + 1)

            -- Assign remaining items to subsequent slots of this type.
            if self:reset_equip_indices(slot, i + 1) then
                return true
            -- There aren't enough unused items left to assign to this slot, so
            -- we're done iterating it.
            else
                break
            end
        end
    end

    -- There are no more unused item combinations for this slot, so reset its
    -- indices to the starting set of items.
    self:reset_equip_indices(slot, 1)
    return false
end

function EquipmentCombinationIterator:slot_iterator(reverse)
    local index, last_index, increment
    if reverse then
        index = #self.inventory_slots
        last_index = 1
        increment = -1
    else
        index = 1
        last_index = #self.inventory_slots
        increment = 1
    end

    return function()
        if index == last_index + increment then
            return
        end

        for i = index, last_index, increment do
            index = i + increment

            if self.active_slots[self.inventory_slots[i]] then
                return self.inventory_slots[i]
            end
        end
    end
end

function EquipmentCombinationIterator:equip_set()
    local equip = {}
    for slot in self:slot_iterator() do
        local inv = self.inventory[slot]
        local indices = self.equip_indices[slot]
        equip[slot] = {}
        for _, ind in ipairs(indices) do
            table.insert(equip[slot], inv[ind])
        end
    end
    return equip
end

function EquipmentCombinationIterator:iterate()
    for slot in self:slot_iterator(true) do
        while self:iterate_equip_slot(slot) do
            if not self.extra_item or self.extra_used then
                return self:equip_set()
            end
        end
    end
end

function equip_combo_iter(inventory, extra_item)
    local iter = EquipmentCombinationIterator:new(inventory, extra_item)
    return function()
        return iter:iterate()
    end
end

function item_in_equip_set(item, equip)
    if not equip then
        return false
    end

    local slot = equip_slot(item)
    if not slot then
        return false
    end

    local name = item.name()
    for eq_item in equip_set_slot_iter(equip, slot) do
        if item.slot and item.slot == eq_item.slot
                or (not item.slot and name == eq_item.name()) then
            return true
        end
    end

    return false
end

function get_swappable_rings(upgrade)
    local swappable_rings = {}
    for _, ring in inventory_slot_iter("ring") do
        if can_swap_item(ring, upgrade) then
            table.insert(swappable_rings, ring)
        end
    end

    return swappable_rings
end

-- This only needs to give the max number of items that can be used for slots
-- the species can actually use.
function slot_max_items(slot)
    if slot == "weapon" then
        return you.race() == "Coglin" and 2 or 1
    elseif slot == "ring" then
        return you.race() == "Octopode" and 8 or 2
    else
        return 1
    end
end

function equip_letter_for_item(item, slot, keep_items, upgrade)
    if not item or item.equipped then
        return
    end

    local cur_equip = inventory_equip(const.inventory.equipped)
    if slot == "weapon"
            and item.hands == 2
            and cur_equip
            and cur_equip.shield then
        return
    end

    if slot == "boots"
            and you.mutation("mertail") > 0
            and (feat == "shallow_water" or feat == "deep_water") then
        return
    end

    local max_items = slot_max_items(slot)
    if max_items == 1
            or not cur_equip[slot]
            or #cur_equip[slot] < max_items then
        return ""
    end

    for slot_item in equipped_slot_iter(slot) do
        if not item_in_equip_set(slot_item, keep_items)
                and can_swap_item(slot_item, upgrade) then
            return item_letter(slot_item)
        end
    end
end

function equip_item(item, slot, keep_items)
    local dest_letter = equip_letter_for_item(item, slot, keep_items, true)
    if not dest_letter then
        return false
    end

    local verb = "WEARING"
    local key = "W"
    if slot == "ring" or slot == "amulet" then
        key = "P"
    elseif slot == "weapon" then
        verb = "WIELDING"
        key = "w"
    end

    say(verb .. " " .. item.name())
    magic(key .. item_letter(item) .. dest_letter)
    return true
end

function unequip_item(item, slot)
    if not item or not item.equipped or not can_swap_item(item, true) then
        return false
    end

    local verb = "REMOVING"
    local key = "T"
    if slot == "ring" or slot == "amulet" then
        key = "R"
    end
    say(verb .. " " .. item.name())
    magic(key .. item_letter(item))
    return true
end

function reset_best_equip()
    c_persist.best_equip = nil
    qw.best_equip = nil
end

function update_equip_tracking()
    if not qw.inventory_equip then
        qw.inventory_equip = {}
    end

    local seen_counts = {}
    for _, item in inventory_slots_iter() do
        local name = item.name()
        local seen = seen_counts[name]
        if seen then
            seen = seen + 1
        else
            seen = 1
        end
        seen_counts[name] = seen

        local prev_count = qw.inventory_equip[name]
        if not prev_count or seen > prev_count then
            if debug_channel("items") then
                dsay("Resetting best equip due to new item: " .. name)
            end

            reset_best_equip()
        end
    end
    qw.inventory_equip = seen_counts

    local xl = you.xl()
    if qw.last_xl ~= xl then
        reset_best_equip()
    end
    qw.last_xl = xl

    update_skill_tracking()
end

function equip_is_valuable_unidentified(item)
    -- DCSS 0.33 removed item.fully_identified. Artefacts are fully
    -- identified exactly when is_identified is true; for other equipment we
    -- check identification state directly below.
    if item.artefact then
        return not item.is_identified
    end

    local slot = equip_slot(item)
    if slot == "ring" or slot == "amulet" then
        -- Since the item identification flags were simplified (DCSS 0.33),
        -- jewellery is identified exactly when is_identified is true.
        -- (Note item.ego() returns nil for unidentified items, so it can't
        -- be used to distinguish unknown jewellery.)
        return not item.is_identified
    end

    local name = item.name()
    if slot == "weapon" then
        return name:find("glowing") or name:find("runed")
    elseif slot == "body" then
        return name:find("glowing")
            or name:find("runed")
            or name:find("shiny")
            or name:find("dyed")
    else
        return name:find("glowing")
            or name:find("runed")
            or name:find("shiny")
            or name:find("embroidered")
    end
end
------------------
-- Goal configuration and assessment

function goal_normal_next(final)
    local goal

    -- Don't try to convert from Ignis too early.
    if explored_level_range("D:1-8")
            and you.god() == "Ignis"
            and you.piety_rank() == 0 then
        local found = {}
        local gods = god_options()
        local keep_ignis = false
        for _, g in ipairs(gods) do
            if g == "Ignis" then
                keep_ignis = true
                break
            elseif altar_found(g) then
                table.insert(found, g)
            end
        end

        if not keep_ignis then
            if #found ~= #gods
                    and branch_found("Temple")
                    and not explored_level_range("Temple") then
                return "Temple"
            end

            if #found > 0 then
                if not c_persist.chosen_god then
                    c_persist.chosen_god = found[crawl.roll_dice(1, #found)]
                end

                return "God:" .. c_persist.chosen_god
            end
        end
    end

    if not explored_level_range("D:1-11") then
        -- We head to Lair early, before having explored through D:11, if we
        -- feel we're ready.
        if branch_found("Lair")
                and not explored_level_range("Lair")
                and ready_for_lair() then
            goal = "Lair"
        else
            goal = "D:1-11"
        end
    -- D:1-11 explored, but not Lair.
    elseif not explored_level_range("Lair") then
        goal = "Lair"
    -- D:1-11 and Lair explored, but not D:12.
    elseif not explored_level_range("D:12") then
        if qw.late_orc then
            goal = "D"
        else
            goal = "D:12"
        end
    -- D:1-12 and Lair explored, but not all of D.
    elseif not explored_level_range("D") then
        if not qw.late_orc
                and branch_found("Orc")
                and not explored_level_range("Orc") then
            goal = "Orc"
        else
            goal = "D"
        end
    -- D and Lair explored, but not Orc.
    elseif not explored_level_range("Orc") then
        goal = "Orc"
    end

    if goal then
        return goal
    end

    -- At this point we're sure we've found Lair branches.
    if not early_first_lair_branch then
        local first_br = next_branch(lair_branch_order())
        early_first_lair_branch = make_level_range(first_br, 1, -1)
        first_lair_branch_end = branch_end(first_br)

        local second_br = next_branch(lair_branch_order(), 1)
        early_second_lair_branch = make_level_range(second_br, 1, -1)
        second_lair_branch_end = branch_end(second_br)
    end

    -- D, Lair, and Orc explored, but no Lair branch.
    if not explored_level_range(early_first_lair_branch) then
        goal = early_first_lair_branch
    -- D, Lair, and Orc explored, levels 1-3 of the first Lair branch.
    elseif not explored_level_range(early_second_lair_branch) then
        goal = early_second_lair_branch
    -- D, Lair, and Orc explored, levels 1-3 of both Lair branches.
    elseif not explored_level_range(first_lair_branch_end) then
        goal = first_lair_branch_end
    -- D, Lair, Orc, and at least one Lair branch explored, but not early
    -- Vaults.
    elseif not explored_level_range(early_vaults) then
        goal = early_vaults
    -- D, Lair, Orc, one Lair branch, and early Vaults explored, but the
    -- second Lair branch not fully explored.
    elseif not explored_level_range(second_lair_branch_end) then
        if not explored_level_range("Depths")
                and not qw.early_second_rune then
            goal = "Depths"
        else
            goal = second_lair_branch_end
        end
    -- D, Lair, Orc, both Lair branches, and early Vaults explored, but not
    -- Depths.
    elseif not explored_level_range("Depths") then
        goal = "Depths"
    -- D, Lair, Orc, both Lair branches, early Vaults, and Depths explored,
    -- but no Vaults rune.
    elseif not explored_level_range(vaults_end) then
        goal = vaults_end
    -- D, Lair, Orc, both Lair branches, Vaults, and Depths explored, and it's
    -- time to shop.
    elseif not c_persist.done_shopping then
        goal = "Shopping"
    -- If we have other goal entries, the Normal plan stops here, otherwise
    -- early Zot.
    elseif final and not explored_level_range(early_zot) then
        goal = early_zot
    -- Time to win.
    elseif final then
        goal = "Win"
    end

    return goal
end

function goal_complete(plan, final)
    if plan:find("^God:") then
        return you.god() == goal_god(plan)
    elseif plan:find("^Rune:") then
        local branch = goal_rune_branch(plan)
        return not branch_exists(branch) or have_branch_runes(branch)
    end

    local branch = parse_level_range(plan)
    return plan == "Normal" and not goal_normal_next(final)
        or branch and not branch_exists(branch)
        or branch and explored_level_range(plan)
        or plan == "Shopping" and c_persist.done_shopping
        or plan == "Abyss"
            and have_branch_runes("Abyss")
        or plan == "Pan" and have_branch_runes("Pan")
        or plan == "Zig" and c_persist.zig_completed
        or plan == "Orb" and qw.have_orb
        or plan == "Save" and c_persist.last_completed_goal == "Save"
end

function choose_goal()
    local next_goal, chosen_goal, normal_goal, last_completed

    if debug_goal then
        if debug_goal == "Normal" then
            normal_goal = goal_normal_next(false)
            if normal_goal then
                chosen_goal = debug_goal
            else
                last_completed = debug_goal
                debug_goal = nil
            end
        elseif goal_complete(debug_goal) then
            last_completed = debug_goal
            debug_goal = nil
        else
            chosen_goal = debug_goal
        end
    end

    while not chosen_goal and which_goal <= #goal_list do
        chosen_goal = goal_list[which_goal]
        next_goal = goal_list[which_goal + 1]
        local chosen_final = not next_goal
        local next_final = not goal_list[which_goal + 2]

        if chosen_goal == "Normal" then
            normal_goal = goal_normal_next(chosen_final)
            if not normal_goal then
                last_completed = chosen_goal
                chosen_goal = nil
            end
        -- For God conversion and save goals, we don't perform them if we see
        -- that the next plan is complete. This way if a goal list has god
        -- conversions or saves, past ones won't be re-attempted when we save
        -- and reload.
        elseif (chosen_goal:find("^God:") or chosen_goal == "Save")
                and next_goal
                and goal_complete(next_goal, next_final) then
            last_completed = chosen_goal
            chosen_goal = nil
        elseif goal_complete(chosen_goal, chosen_final) then
            last_completed = chosen_goal
            chosen_goal = nil
        end

        if not chosen_goal then
            which_goal = which_goal + 1
        end
    end

    if last_completed then
        c_persist.last_completed_goal = last_completed
    end

    -- We're out of goals, so we make our final task be winning.
    if not chosen_goal then
        which_goal = nil
        chosen_goal = "Win"
    end

    return chosen_goal, normal_goal
end

-- Choose an active portal on this level. We only consider allowed portals, and
-- choose the oldest one. Permanent bazaars get chosen last.
function choose_level_portal(level)
    local oldest_portal
    local oldest_turns
    for portal, turns_list in pairs(c_persist.portals[level]) do
        if portal_allowed(portal) then
            if #turns_list > 0
                    and (not oldest_turns
                        or turns_list[#turns_list] < oldest_turns) then
                oldest_portal = portal
                oldest_turns = turns_list[#turns_list]
            end
        end
    end

    return oldest_portal, oldest_turns
end

-- If we found a viable portal on the current level, that becomes our goal.
function get_portal_goal()
    local chosen_portal, chosen_level, chosen_turns
    for level, portals in pairs(c_persist.portals) do
        local portal, turns = choose_level_portal(level)
        if portal and (not chosen_turns or turns < chosen_turns) then
            chosen_portal = portal
            chosen_level = level
            chosen_turns = turns
        end
    end

    -- We only load a portal's parent branch info when it's actually chosen,
    -- and the parent info will be removed once the portal expires or is
    -- completed.
    if chosen_portal then
        local branch, depth = parse_level_range(chosen_level)
        branch_data[chosen_portal].parent = branch
        branch_data[chosen_portal].parent_min_depth = depth
        branch_data[chosen_portal].parent_max_depth = depth
    end

    return chosen_portal, chosen_turns == const.inf_turns
end

function want_god()
    return you.race() ~= "Demigod"
        and you.god() == "No God"
        and god_options()[1] ~= "No God"
end

function determine_goal()
    permanent_bazaar = nil
    local chosen_goal, normal_goal = choose_goal()
    local old_status = goal_status
    local status = chosen_goal
    local goal = status

    if status == "Save" then
        goal_status = status
        say("SAVING")
        return
    end

    if qw.quit_turns and qw.stuck_turns > qw.quit_turns
            or select(2, you.hp()) == 1 then
        status = "Quit"
    end

    if status == "Quit" then
        goal_status = status
        say("QUITTING!")
        return
    end

    if status == "Normal" then
        status = normal_goal
        goal = normal_goal
    end

    -- Once we have the rune for this branch, this goal will be complete.
    -- Until then, we're diving to and exploring the branch end.
    local desc
    if status:find("^Rune:") then
        local branch = goal_rune_branch(status)
        goal = make_level(branch, branch_rune_depth(branch))
        desc = branch .. " rune"
    end

    -- If we're configured to join a god, prioritize finding one from our god
    -- list, possibly exploring Temple once it's found.
    if want_god() then
        local found = {}
        local gods = god_options()
        for _, g in ipairs(gods) do
            if altar_found(g) then
                table.insert(found, g)
            end
        end

        if #found ~= #gods
                and branch_found("Temple")
                and not explored_level_range("Temple") then
            status = "Temple"
            goal = "Temple"
            desc = "Temple"
        elseif #found > 0 then
            if not c_persist.chosen_god then
                c_persist.chosen_god = found[crawl.roll_dice(1, #found)]
            end

            status = "God:" .. c_persist.chosen_god
        end
    end

    if status:find("^God:") then
        local god = goal_god(status)
        desc = god .. " worship"
        local altar_level = altar_found(god)
        if altar_level then
            goal = altar_level
        elseif branch_found("Temple")
                and not explored_level_range("Temple") then
            goal = "Temple"
        end
    end

    local portal
    portal, permanent_bazaar = get_portal_goal()
    if portal then
        status = portal
        goal = portal
        desc = portal
    end

    -- Make sure we respect Vaults locking when we don't have the rune.
    if in_branch("Vaults") and you.num_runes() == 0 then
        local branch = parse_level_range(goal)
        local override = false
        if branch then
            local parent = parent_branch(branch)
            if branch ~= "Vaults"
                    and parent ~= "Vaults"
                    and parent ~= "Crypt"
                    and parent ~= "Tomb" then
                override = true
            end
        else
            override = true
        end

        if override then
            branch = "Vaults"
            status = "Rune:Vaults"
            goal = vaults_end
            desc = "Vaults rune"
        end
    end

    if status == "Win" then
        status = qw.have_orb and "Escape" or "Orb"
    end

    if status == "Escape" then
        goal = "D:1"
    -- Dive to and explore the end of Zot. We'll start trying to pick up the
    -- ORB via stash search travel as soon as it's found.
    elseif status == "Orb" then
        goal = zot_end
    end

    -- Portals remain our goal while we're there.
    if in_portal() then
        status = where_branch
        goal = where_branch
    end

    local branch = parse_level_range(goal)
    if branch == "Zot" and you.num_runes() < 3 then
        error("Couldn't get three runes to enter Zot!")
    end

    if old_status ~= status then
        if not desc then
            if status == "Shopping" then
                desc = "shopping spree"
            else
                desc = status
            end
        end
        say("PLANNING " .. desc:upper())
    end

    set_goal(status, goal)
end

function branch_soon(branch)
    return branch == goal_branch
end

function undead_or_demon_branch_soon()
    return branch_soon("Abyss")
        or branch_soon("Crypt")
        or branch_soon("Hell")
        or is_hell_branch(goal_branch)
        or branch_soon("Pan")
        or branch_soon("Tomb")
        or branch_soon("Zig")
        -- Once you have the ORB, every branch is an demon branch.
        or qw.have_orb
end

function goals_visit_branches(branches)
    if not which_goal then
        return false
    end

    for i = which_goal, #goal_list do
        local plan = goal_list[i]
        local plan_branch
        if plan:find("^Rune:") then
            plan_branch = goal_rune_branch(plan)
        else
            plan_branch = parse_level_range(plan)
        end

        if plan_branch
                and util.contains(branches, plan_branch)
                and not goal_complete(plan, i == #goal_list) then
            return true
        end
    end

    if not qw.have_orb and util.contains(branches, "Zot") then
        return true
    end

    return false
end

function goals_visit_branch(branch)
    return goals_visit_branches({ branch })
end

function goals_future_gods()
    if not which_goal then
        return {}
    end

    local options = god_options()
    local gods = {}
    if not util.contains(options, you.god()) then
        gods = util.copy_table(options)
    end

    for i = which_goal, #goal_list do
        local plan = goal_list[i]
        local plan_god = goal_god(plan)
        if plan_god then
            table.insert(gods, plan_god)
        end
    end

    return gods
end

function planning_convert_to_gods(gods)
    for _, god in ipairs(gods) do
        if util.contains(qw.future_gods, god) then
            return true
        end
    end

    return false
end

function planning_convert_to_god(god)
    return planning_convert_to_gods({ god })
end

function planning_convert_to_mp_using_gods()
    if you.race() == "Djinni" then
        return false
    end

    return planning_convert_to_gods(const.mp_using_gods)
end

function planned_gods_all_use_mp()
    if not util.contains(const.mp_using_gods, you.god()) then
        return false
    end

    for _, god in ipairs(qw.future_gods) do
        if not util.contains(const.mp_using_gods, god) then
            return false
        end
    end

    return true
end

function update_planning()
    if goal_status == "Save" or goal_status == "Quit" then
        return
    end

    qw.planning_zig = goals_visit_branch("Zig")

    qw.planning_vaults = goals_visit_branch("Vaults")
    qw.planning_slime = goals_visit_branch("Slime")
    qw.planning_tomb = goals_visit_branch("Tomb")
    qw.planning_cocytus = goals_visit_branch("Coc")

    qw.future_gods = goals_future_gods()
    qw.future_gods_use_mp = planning_convert_to_mp_using_gods()
    qw.future_tso = planning_convert_to_god("the Shining One")
    qw.future_okawaru = planning_convert_to_god("Okawaru")

    qw.planned_gods_all_use_mp = planned_gods_all_use_mp()
end

-- Make a level range for the given branch and ranges, e.g. D:1-11. The
-- returned string is normalized so it's as simple as possible. Invalid level
-- ranges raise an error.
-- @string      branch The branch.
-- @number      first  The first level in the range.
-- @number[opt] last   The last level in the range, defaulting to the branch end.
--                     If negative, the range stops that many levels from the
--                     end of the branch.
-- @treturn string The level range.
function make_level_range(branch, first, last)
    local max_depth = branch_depth(branch)
    if not last then
        last = max_depth
    elseif last < 0 then
        last = max_depth + last
    end

    if first < 1
            or first > max_depth
            or last < 1
            or last > max_depth
            or first > last then
        error("Invalid level range for " .. tostring(branch)
            ..": " .. tostring(first) .. ", " .. tostring(last))
    end

    if first == 1 and last == max_depth then
        return branch
    elseif first == last then
        return branch .. ":" .. first
    else
        return branch .. ":" .. first .. "-" .. last
    end
end

-- Make a level range for a single level, e.g. D:1.
-- @string branch The branch.
-- @int    first  The level.
-- @treturn string The level range.
function make_level(branch, depth)
    return make_level_range(branch, depth, depth)
end

-- Parse components of a level range.
-- @string range The level range.
--
-- @treturn string The branch. Will be nil if the level is invalid.
-- @treturn int    The starting level.
-- @treturn int    The ending level.
function parse_level_range(range)
    local terms = split(range, ":")
    local br = terms[1]

    if not branch_data[br] then
        return
    end

    local br_depth = branch_depth(br)
    -- A branch name with no level range.
    if #terms == 1 then
        return br, 1, br_depth
    end

    local min_level, max_level
    local level_terms = split(terms[2], "-")
    min_level = tonumber(level_terms[1])
    if not min_level
            or math.floor(min_level) ~= min_level
            or min_level < 1
            or min_level > br_depth then
        return
    end

    if #level_terms == 1 then
        max_level = min_level
    else
        max_level = tonumber(level_terms[2])
        if not max_level
                or math.floor(max_level) ~= max_level
                or max_level < min_level
                or max_level > br_depth then
            return
        end
    end

    return br, min_level, max_level
end

function autoexplored_level(branch, depth)
    local state = c_persist.autoexplore[make_level(branch, depth)]
    return state and state > const.autoexplore.needed
end

function explored_level(branch, depth)
    if branch == "Abyss" or branch == "Pan" then
        return have_branch_runes(branch)
    end

    return autoexplored_level(branch, depth)
        and have_all_stairs(branch, depth, const.dir.down,
            const.explore.reachable)
        and have_all_stairs(branch, depth, const.dir.up,
            const.explore.reachable)
        and (have_branch_runes(branch) or depth < branch_rune_depth(branch))
end

function explored_level_range(range)
    local br, min_level, max_level
    br, min_level, max_level = parse_level_range(range)
    if not br then
        return false
    end

    for l = min_level, max_level do
        if not explored_level(br, l) then
            return false
        end
    end

    return true
end

function ready_for_lair()
    if want_god()
            or goal_branch
                and goal_branch == "D"
                and goal_depth <= 11
                and not explored_level(goal_branch, goal_depth) then
        return false
    end

    return you.god() == "Trog"
        or you.god() == "Cheibriados"
        or you.god() == "Okawaru"
        or you.god() == "Ignis"
        or you.god() == "Qazlal"
        or you.god() == "the Shining One"
        or you.god() == "Lugonu"
        or you.god() == "Uskayaw"
        or you.god() == "Xom"
        or you.god() == "Zin"
        or (you.god() == "Beogh"
            or you.god() == "Makhleb"
            or you.god() == "Yredelemnul") and you.piety_rank() >= 4
        or (you.god() == "Ru" or you.god() == "Elyvilon")
            and you.piety_rank() >= 3
        or you.god() == "Hepliaklqana" and you.piety_rank() >= 2
end

-- Return the next existing level range in a list.
-- @param[opt=0] skip A number giving how many valid level ranges to skip.
-- @tparam options A list of level ranges.
-- @treturn string The next level range.
function next_branch(options, skip)
    if not skip then
        skip = 0
    end

    local skipped = 0
    for _, level in ipairs(options) do
        local branch = parse_level_range(level)
        -- Reject any levels in branches that couldn't exist given the branches
        -- we've found already.
        if branch and branch_exists(branch) then
            if skipped < skip then
                skipped = skipped + 1
            else
                return branch
            end
        end
    end
end

function lair_branch_order()
    if c_persist.lair_branch_order then
        return c_persist.lair_branch_order
    end

    local branch_options
    if qw.rune_preference == "smart" then
        if crawl.random2(2) == 0 then
            branch_options = { "Spider", "Snake", "Swamp", "Shoals" }
        else
            branch_options = { "Spider", "Swamp", "Snake", "Shoals" }
        end
    elseif qw.rune_preference == "dsmart" then
        if crawl.random2(2) == 0 then
            branch_options = { "Spider", "Swamp", "Snake", "Shoals" }
        else
            branch_options = { "Swamp", "Spider", "Snake", "Shoals" }
        end
    elseif qw.rune_preference == "nowater" then
        branch_options = { "Snake", "Spider", "Swamp", "Shoals" }
    -- "random"
    else
        if crawl.random2(2) == 0 then
            branch_options = { "Snake", "Spider", "Swamp", "Shoals" }
        else
            branch_options = { "Swamp", "Shoals", "Snake", "Spider" }
        end
    end

    c_persist.lair_branch_order = branch_options
    return branch_options
end

-- Remove the "God:" prefix and return the god's full name.
function goal_god(plan)
    if not plan:find("^God:") then
        return
    end

    return god_full_name(plan:sub(5))
end

-- Remove the "Rune:" prefix and return the branch name.
function goal_rune_branch(plan)
    if not plan:find("^Rune:") then
        return
    end

    return plan:sub(6)
end

-- Remove any prefix and return the Zig depth we want to reach.
function goal_zig_depth(plan)
    if plan == "Zig" or plan:find("^MegaZig") then
        return 27
    end

    if not plan:find("^Zig:") then
        return
    end

    return tonumber(plan:sub(5))
end

function initialize_goals()
    local goals = split(goal_options(), ",")
    goal_list = {}
    for _, pl in ipairs(goals) do
        -- Two-part plan specs: God conversion and rune.
        local plan
        pl = trim(pl)
        if pl:lower():find("^god:") then
            local name = goal_god(pl)
            if not name then
                error("Unkown god: " .. name)
            end

            plan = "God:" .. name
            processed = true
        elseif pl:lower():find("^rune:") then
            local branch = capitalise(goal_rune_branch(pl))
            if not branch_data[branch] then
                error("Unknown rune branch: " .. branch)
            elseif not branch_runes(branch) then
                error("Branch has no rune: " .. branch)
            end

            plan = "Rune:" .. branch
            processed = true
        else
            -- Normalize the plan so we're always making accurate comparisons
            -- for special plans like Normal, Shopping, Orb, etc.
            plan = capitalise(pl)
        end

        -- We turn Hells into a sequence of goals for each Hell branch rune
        -- in random order.
        if plan == "Hells" then
            -- Save our selection so it can be recreated across saving.
            if not c_persist.hell_branches then
                c_persist.hell_branches = util.random_subset(hell_branches,
                    #hell_branches)
            end

            for _, br in ipairs(c_persist.hell_branches) do
                table.insert(goal_list, "Rune:" .. br)
            end
        end

        local branch, min_level, max_level = parse_level_range(plan)
        if not (branch
                or plan == "Save"
                or plan == "Quit"
                or plan == "Escape"
                or plan:find("^Rune:")
                or plan:find("^God:")
                or plan == "Normal"
                or plan == "Shopping"
                or plan == "Hells"
                or plan == "Zig"
                or plan == "Orb"
                or plan == "Win") then
            error("Invalid goal '" .. tostring(plan) .. "'.")
        end

        table.insert(goal_list, plan)
    end
end

function update_goal()
    local last_goal_branch = goal_branch

    update_expired_portals()
    update_permanent_flight()

    determine_goal()
    update_planning()
    update_goal_travel()

    open_runed_doors = branch_is_temporary(where_branch)
        or goal_travel.open_runed_doors

    -- The branch we're planning to visit can affect equipment decisions.
    if last_goal_branch ~= goal_branch then
        reset_best_equip()
    end

    qw.want_goal_update = false
end

function god_options()
    return c_persist.current_god_list
end

function goal_options()
    if override_goals then
        return override_goals
    end

    return qw.goals[c_persist.current_goals]
end

function next_exploration_depth(branch, min_depth, max_depth)
    if branch == "Abyss" then
        local rune_depth = branch_rune_depth("Abyss")
        if in_branch("Abyss") and where_depth > rune_depth then
            return where_depth
        else
            return rune_depth
        end
    end

    -- The earliest depth that either lacks autoexplore or doesn't have all
    -- stairs reachable.
    local branch_max = branch_depth(branch)
    for d = min_depth, max_depth do
        if not autoexplored_level(branch, d) then
            return d
        elseif not have_all_stairs(branch, d, const.dir.up,
                    const.explore.reachable)
                or not have_all_stairs(branch, d, const.dir.down,
                    const.explore.reachable) then
            return d
        end
    end

    if max_depth == branch_depth(branch) and not have_branch_runes(branch) then
        return max_depth
    end
end

function set_goal(status, goal)
    goal_status = status

    goal_branch = nil
    goal_depth = nil
    local min_depth, max_depth
    goal_branch, min_depth, max_depth = parse_level_range(goal)

    -- God and Escape goals always set the goal branch/depth to a
    -- specific level, so we don't need further exploration.
    if status:find("^God") or status == "Escape" then
        goal_depth = min_depth
    elseif in_portal() then
        goal_depth = where_depth
    elseif goal_branch then
        goal_depth
            = next_exploration_depth(goal_branch, min_depth, max_depth)

        if goal == zot_end and not goal_depth then
            goal_depth = branch_depth("Zot")
            if where == zot_end then
                qw.ignore_traps = true
                c_persist.autoexplore[zot_end] = const.autoexplore.needed
            end
        end
    end

    if debug_channel("goals") then
        dsay("Goal status: " .. goal_status)
        if goal_branch then
            dsay("Goal branch: " .. tostring(goal_branch)
                .. ", depth: " .. tostring(goal_depth))
        end
    end
end

function reset_autoexplore(level)
    if c_persist.autoexplore[level] == const.autoexplore.needed then
        return
    end

    if debug_channel("goals") then
        dsay("Resetting autoexplore of " .. level)
    end

    c_persist.autoexplore[level] = const.autoexplore.needed
    qw.want_goal_update = true
end
------------------
-- Start of game and session initialization.

function cleanup_feature_state(state)
    if state.safe == nil then
        state.safe = true
    end
    if state.feat == nil then
        state.feat = const.explore.none
    end
    if state.threat == nil then
        state.threat = 0
    end
end

function cleanup_feature_table(feat_table, table_level)
    for key, inner_table in pairs(feat_table) do
        if table_level == 1 then
            cleanup_feature_state(inner_table)
        else
            cleanup_feature_table(inner_table, table_level - 1)
        end
    end
end

function cleanup_c_persist_features()
    cleanup_feature_table(c_persist.upstairs, 2)
    cleanup_feature_table(c_persist.downstairs, 2)

    cleanup_feature_table(c_persist.branch_exits, 2)
    cleanup_feature_table(c_persist.branch_entries, 2)

    cleanup_feature_table(c_persist.up_hatches, 2)
    cleanup_feature_table(c_persist.down_hatches, 2)

    cleanup_feature_table(c_persist.altars, 3)

    cleanup_feature_table(c_persist.abyssal_stairs, 1)
end

function initialize_c_persist()
    if not c_persist.waypoint_count then
        c_persist.waypoint_count = 0
    end

    local tables = {
        "abyssal_stairs", "altars", "autoexplore", "branch_entries",
        "branch_exits", "down_hatches", "downstairs", "exclusions",
        "expiring_portals", "pan_transits", "plan_fail_count", "portals",
        "potion_ident", "scroll_ident", "seen_items",
        "up_hatches", "upstairs", "waypoints",
    }
    for _, table in ipairs(tables) do
        if not c_persist[table] then
            c_persist[table] = {}
        end
    end

    cleanup_c_persist_features()
end

function initialize_rc_variables()
    if MAX_MEMORY then
        qw.max_memory = MAX_MEMORY * 1024
    end

    qw.coroutine_throttle = COROUTINE_THROTTLE

    qw.delayed = DELAYED
    qw.delay_time = DELAY_TIME

    qw.single_step = SINGLE_STEP
    if AUTO_START then
        qw.automatic = true
    end

    qw.quit_turns = QUIT_TURNS
    qw.wizmode_death = WIZMODE_DEATH

    qw.combo_cycle = COMBO_CYCLE
    qw.combo_cycle_list = COMBO_CYCLE_LIST
    qw.goals = GOALS
    qw.default_goal = DEFAULT_GOAL
    qw.future_gods = {}

    qw.god_list = GOD_LIST
    qw.faded_altar = FADED_ALTAR
    qw.ck_abandon_xom = CK_ABANDON_XOM

    qw.allowed_portals = ALLOWED_PORTALS
    qw.early_second_rune = EARLY_SECOND_RUNE
    qw.late_orc = LATE_ORC
    qw.rune_preference = RUNE_PREFERENCE

    qw.shield_crazy = SHIELD_CRAZY and you.race() ~= "Coglin"
    qw.full_inventory_panic = FULL_INVENTORY_PANIC
end

function initialize_enums()
    const.autoexplore = enum(const.autoexplore)
    const.explore = enum(const.explore)
    const.map_select = enum(const.map_select)
    const.attitude = enum(const.attitude)
    const.duration = enum(const.duration)
    const.inventory = enum(const.inventory)
    const.attack = enum(const.attack)
end

function initialize_const()
    initialize_enums()
    initialize_player_durations()
    initialize_ego_damage()
end

function initialize()
    -- The version of qw for logging purposes. Run the make-qw.sh script to set
    -- this variable automatically based on the latest annotated git tag and
    -- commit, or change it here to a custom version string.
    qw.version = "0.4-a-66-g8698adc"

    initialize_rc_variables()

    initialize_debug()
    initialize_const()
    initialize_plan_cascades()
    initialize_c_persist()

    if not cache_parity then
        traversal_maps_cache = {}
        adjacent_floor_maps_cache = {}
        exclusion_maps_cache = {}

        distance_maps_cache = {}
        feature_map_positions_cache = {}
        item_map_positions_cache = {}
        map_mode_searches_cache = {}

        clear_map_cache(1, true)
        clear_map_cache(2, true)

        cache_parity = 1
    end

    if you.turns() == 0 then
        initialize_branch_data()
        initialize_god_data()
    end

    initialize_branch_data()
    initialize_god_data()

    first_turn_initialize()
    initialize_c_persist()

    note_qw_data()

    calc_los_radius()
    initialize_monster_map()

    initialize_goals()
    qw.starting_spell = get_starting_spell()

    set_options()

    clear_autopickup_funcs()
    add_autopickup_func(autopickup)

    qw.turn_count = you.turns() - 1
    qw.dump_count = you.turns() + 100 - (you.turns() % 100)
    qw.skill_count = you.turns() - (you.turns() % 5)
    qw.read_message = true

    qw.incoming_monsters_turn = -1
    qw.full_hp_turn = -1

    qw.initialized = true
end

function note_qw_data()
    note("qw: Version: " .. qw.version)
    note("qw: Game counter: " .. c_persist.record.counter)
    note("qw: Melee chars always use a shield: " .. bool_string(qw.shield_crazy))

    if not util.contains(god_options(), you.god()) then
        note("qw: God list: " .. table.concat(god_options(), ", "))
        note("qw: Allow faded altars: " .. bool_string(qw.faded_altar))
    end

    note("qw: Do Orc after clearing Dungeon:" .. branch_depth("D") .. " "
        .. bool_string(qw.late_orc))
    note("qw: Do second Lair branch before Depths: " ..
        bool_string(qw.early_second_rune))
    note("qw: Lair rune preference: " .. qw.rune_preference)
    note("qw: Goals: " .. goal_options())
end

function first_turn_initialize()
    if you.turns() > 0 and c_persist.record then
        return
    end

    if not c_persist.record then
        c_persist.record = {}
    end

    local counter = c_persist.record.counter
    if not counter then
        counter = 1
    else
        counter = counter + 1
    end
    c_persist.record.counter = counter

    local god_list = c_persist.next_god_list
    local goals = c_persist.next_goals
    for key, _ in pairs(c_persist) do
        if key ~= "record" then
            c_persist[key] = nil
        end
    end

    if not god_list then
        if qw.god_list and #qw.god_list > 0 then
            god_list = qw.god_list
        else
            error("No default god list defined in GOD_LIST rc variable.")
        end
    end

    -- Check for and normalize a list with "No God"
    local no_god = false
    for _, god in ipairs(god_list) do
        if god_full_name(god) == "No God" then
            no_god = true
            break
        end
    end
    if no_god then
        if #god_list > 1 then
            error("God list containing 'No God' must have no other entries.")
        else
            god_list = {"No God"}
        end
    end
    c_persist.current_god_list = god_list

    if not goals then
        goals = qw.default_goal
        if not goals then
            error("No default goal defined in DEFAULT_GOAL rc varaible.")
        end
    end
    c_persist.current_goals = goals

    if qw.combo_cycle then
        local combo_string_list = split(qw.combo_cycle_list, ",")
        local combo_string = combo_string_list[
            1 + (c_persist.record.counter % (#combo_string_list))]
        combo_string = trim(combo_string)
        local combo_parts = split(combo_string, "^")
        c_persist.options = "combo = " .. combo_parts[1]
        if #combo_parts > 1 then
            local goal_parts = split(combo_parts[2], "!")
            c_persist.next_god_list = {}
            for g in goal_parts[1]:gmatch(".") do
                table.insert(c_persist.next_god_list, god_full_name(g))
            end
            if #goal_parts > 1 then
                if not qw.goals[goal_parts[2]] then
                    error("Unknown goal name '" .. goal_parts[2] .. "'"
                        ..  " given in combo spec '" .. combo_string .. "'")
                end
                c_persist.next_goals = goal_parts[2]
            end
        end
    end
end
-------------------
-- Some general input and message output handling, as well as in-game message
-- parsing.

function note(x)
    crawl.take_note(you.turns() .. " ||| " .. x)
end

function say(x)
    crawl.mpr(you.turns() .. " ||| " .. x)
    note(x)
end

function magic(command)
    crawl.process_keys(command .. string.char(27) .. string.char(27)
        .. string.char(27))
end

function magicfind(target, secondary)
    if secondary then
        crawl.sendkeys(control('f') .. target .. "\r", arrowkey('d'), "\r\r" ..
            string.char(27) .. string.char(27) .. string.char(27))
    else
        magic(control('f') .. target .. "\r\r\r")
    end
end

function c_answer_prompt(prompt)
    if prompt == "Die?" then
        return qw.wizmode_death
    elseif prompt:find("This attack would place you under penance") then
        return false
    elseif prompt:find("Shopping list") then
        return false
    elseif prompt:find("Keep")
            and (prompt:find("removing")
                or prompt:find("disrobing")
                or prompt:find("equipping")) then
        return false
    elseif prompt:find("Have to go through") then
        return true
    elseif prompt:find("unable to climb back up again") then
        -- Entering the Slime Pits before the Royal Jelly is dead (DCSS 0.34
        -- slimy stairs); we only enter Slime when getting its rune, and
        -- killing the Royal Jelly reopens the stairs.
        return true
    elseif prompt:find("transient mutations") then
        return true
    elseif prompt:find("Really")
            and (prompt:find("take off")
                or prompt:find("remove")
                or prompt:find("wield")
                or prompt:find("wear")
                or prompt:find("put on")
                or prompt:find("read")
                or prompt:find("drink")
                or prompt:find("quaff")
                or prompt:find("rampage")
                or prompt:find("fire at your")
                or prompt:find("fire in the non-hostile")
                or prompt:find("explore while Zot is near")
                or prompt:find(".*into that.*trap")
                or prompt:find("abort")) then
        return true
    elseif prompt:find("You cannot afford")
            and prompt:find("travel there anyways") then
        return true
    elseif prompt:find("Are you sure you want to drop") then
        return true
    elseif prompt:find("next level anyway") then
        return true
    elseif prompt:find("into the Zot trap") then
        return true
    elseif prompt:find("beam is likely to hit you") then
        return true
    end
end

function control(c)
    return string.char(string.byte(c) - string.byte('a') + 1)
end

local a2c = { ['u'] = -254, ['d'] = -253, ['l'] = -252 ,['r'] = -251 }
function arrowkey(c)
    return a2c[c]
end

local d2v = {
    [-1] = { [-1] = 'y', [0] = 'h', [1] = 'b' },
    [0]  = { [-1] = 'k', [1] = 'j' },
    [1]  = { [-1] = 'u', [0] = 'l', [1] = 'n' },
}
local v2d = {}
for x, _ in pairs(d2v) do
    for y, c in pairs(d2v[x]) do
        v2d[c] = { x = x, y = y }
    end
end

function delta_to_vi(pos)
    return d2v[pos.x][pos.y]
end

function vi_to_delta(c)
    return v2d[c]
end

function vector_move(pos)
    local str = ''
    for i = 1, abs(pos.x) do
        str = str .. delta_to_vi({ x = sign(pos.x), y = 0 })
    end
    for i = 1, abs(pos.y) do
        str = str .. delta_to_vi({ x = 0, y = sign(pos.y) })
    end
    return str
end

function ch_stash_search_annotate_item(it)
    return ""
end

function remove_message_tags(text)
    return text:gsub("<[^>]+>(.-)</[^>]+>", "%1")
end

-- A hook for incoming game messages. Note that this is executed for every new
-- message regardless of whether turn_update() this turn (e.g during
-- autoexplore or travel)). Hence this function shouldn't depend on any state
-- variables managed by turn_update(). Use the clua interfaces like you.where()
-- directly to get info about game status.
function c_message(text, channel)
    if text:find("Your surroundings suddenly seem different") then
        invis_monster = false
    elseif text:find("Your pager goes off") then
        qw.have_message = true
    elseif text:find("Done exploring") then
        local where = you.where()
        if c_persist.autoexplore[where] ~= const.autoexplore.full then
            c_persist.autoexplore[where] = const.autoexplore.full
            qw.want_goal_update = true
        end
    elseif text:find("Partly explored") then
        local where = you.where()
        if text:find("transporter") then
            if c_persist.autoexplore[where] ~= const.autoexplore.transporter then
                c_persist.autoexplore[where] = const.autoexplore.transporter
                qw.want_goal_update = true
            end
        else
            if c_persist.autoexplore[where] ~= const.autoexplore.partial then
                c_persist.autoexplore[where] = const.autoexplore.partial
                qw.want_goal_update = true
            end
        end
    elseif text:find("Could not explore") then
        local where = you.where()
        if c_persist.autoexplore[where] ~= const.autoexplore.runed_door then
            c_persist.autoexplore[where] = const.autoexplore.runed_door
            qw.want_goal_update = true
        end
    -- Track which stairs we've fully explored by watching pairs of messages
    -- corresponding to standing on stairs and then taking them. The climbing
    -- message happens before the level transition.
    elseif text:find("You climb downwards")
            or text:find("You fly downwards")
            or text:find("You climb upwards")
            or text:find("You fly upwards") then
        stairs_travel = view.feature_at(0, 0)
    -- Record the staircase if we had just set stairs_travel.
    elseif text:find("There is a stone staircase") then
        if stairs_travel then
            local feat = view.feature_at(0, 0)
            local dir, num = stone_stairs_type(feat)
            local travel_dir, travel_num = stone_stairs_type(stairs_travel)
            -- Sanity check to make sure the stairs correspond.
            if travel_dir and dir and travel_dir == -dir
                    and travel_num == num then
                local branch, depth = parse_level_range(you.where())
                update_stone_stairs(branch, depth, dir, num,
                    { feat = const.explore.explored })
                update_stone_stairs(branch, depth + dir, travel_dir,
                    travel_num, { feat = const.explore.explored })
            end
        end
        stairs_travel = nil
    elseif text:find("You pick up the.*rune and feel its power") then
        qw.want_goal_update = true
    elseif text:find("abyssal rune vanishes from your memory and reappears")
            or text:find("detect the abyssal rune") then
        c_persist.sense_abyssal_rune = true
    -- Timed portals are recorded by the "Hurry and find it" message handling,
    -- but a permanent bazaar doesn't have this. Check messages for "a gateway
    -- to a bazaar", which happens via autoexplore. Timed bazaars are described
    -- as "a flickering gateway to a bazaar", so by looking for the right
    -- message, we prevent counting timed bazaars twice.
    elseif text:find("abyssal rune vanishes from your memory") then
        c_persist.sense_abyssal_rune = false
    elseif text:find("potion of [%a ]+%.") then
        text = remove_message_tags(text)
        record_item_ident("potion",
            text:gsub(".*potion of ([%a ]+)%..*", "%1"))
    elseif text:find("scroll of [%a ]+%.") then
        text = remove_message_tags(text)
        record_item_ident("scroll",
            text:gsub(".*scroll of ([%a ]+)%..*", "%1"))
    elseif text:find("Found a gateway to a bazaar") then
        record_portal(you.where(), "Bazaar", true)
    elseif text:find("Hurry and find it")
            or text:find("Find the entrance") then
        for portal, _ in pairs(portal_data) do
            if text:lower():find(portal_description(portal):lower()) then
                record_portal(you.where(), portal)
                break
            end
        end
    elseif record_portal_final_message(you.where(), text) then
        return
    elseif text:find("The walls and floor vibrate strangely") then
        remove_expired_portal(you.where())
    elseif text:find("You enter the transporter") then
        transp_zone = transp_zone + 1
        transp_orient = true
    elseif text:find("You enter a dispersal trap")
            or text:find("You enter a permanent teleport trap") then
        qw.ignore_traps = false
    elseif text:find("You feel very bouyant") then
        temporary_flight = true
    elseif text:find("You pick up the Orb of Zot") then
        qw.want_goal_update = true
    elseif text:find("Zot's power touches on you") then
        qw.want_goal_update = true
    elseif text:find("You die...") then
        crawl.sendkeys(string.char(27) .. string.char(27)
            .. string.char(27))
    end
end
-------------------------------------
-- General item usage and autopickup

const.rune_suffix = " rune of Zot"
const.orb_name = "Orb of Zot"

const.wand_types = { "flame", "mindburst", "iceblast", "acid", "light",
    "quicksilver", "paralysis" }

function item_is_penetrating(item)
    if item.ego() == "penetration" or item.name():find("storm bow") then
        return true
    end

    local class = item.class(true)
    local subtype = item.subtype()
    return subtype == "javelin"
        or class == "wand"
            and (subtype == "acid"
                or subtype == "light"
                or subtype == "quicksilver")
end

function item_is_exploding(item)
    if item.name():find("{damnation}") then
        return true
    end

    if item.class(true) == "wand" then
        local subtype = item.subtype()
        return subtype == "iceblast" or subtype == "roots"
    end

    return false
end

function item_explosion_ignores_player(item)
    return item.name():find("{damnation}")
        or item.class(true) == "wand" and item.subtype() == "roots"
end

function item_range(item)
    if item.class(true) == "wand" then
        local subtype = item.subtype()
        if subtype == "acid"
                or subtype == "iceblast"
                or subtype == "light"
                or subtype == "roots" then
            return 5
        else
            return qw.los_radius
        end
    end

    return qw.los_radius
end

function item_can_target_empty(item)
    return item.class(true) == "wand" and item.subtype() == "iceblast"
end

function count_charges(wand_type)
    local count = 0
    for item in inventory_iter() do
        if item.class(true) == "wand" and item.subtype() == wand_type then
            count = count + item.plus
        end
    end
    return count
end

function want_wand(item)
    if you.mutation("inability to use devices") > 0 then
        return false
    end

    local subtype = item.subtype()
    if not subtype then
        return true
    end

    if not util.contains(const.wand_types, subtype) then
        return false
    end

    if subtype == "flame" then
        return you.xl() <= 8
    elseif subtype == "mindburst" then
        return you.xl() <= 17
    else
        return true
    end
end

function want_potion(item)
    local subtype = item.subtype()
    if not subtype then
        return true
    end

    local wanted = { "cancellation", "curing", "enlightenment", "experience",
        "heal wounds", "haste", "resistance", "might", "mutation",
        "cancellation" }

    if god_uses_mp() or qw.future_gods_use_mp then
        table.insert(wanted, "magic")
    end

    if qw.planning_tomb then
        table.insert(wanted, "lignification")
        table.insert(wanted, "attraction")
    end

    return util.contains(wanted, subtype)
end

function want_scroll(item)
    local subtype = item.subtype()
    if not subtype then
        return true
    end

    local wanted = { "acquirement", "brand weapon", "enchant armour",
        "enchant weapon", "identify", "teleportation"}

    if qw.planning_zig then
        table.insert(wanted, "blinking")
        table.insert(wanted, "fog")
    end

    return util.contains(wanted, subtype)
end

function want_missile(item)
    if item.is_useless or using_ranged_weapon(true) then
        return false
    end

    local st = item.subtype()
    return st == "boomerang" or st == "javelin" or st == "large rock"
end

function want_miscellaneous(item)
    local subtype = item.subtype()
    if subtype == "figurine of a ziggurat" then
        return qw.planning_zig
    end

    return false
end

function record_seen_item(level, name)
    if not c_persist.seen_items[level] then
        c_persist.seen_items[level] = {}
    end

    c_persist.seen_items[level][name] = true
end

function have_quest_item(name)
    return name:find(const.rune_suffix)
            and you.have_rune(name:gsub(const.rune_suffix, ""))
        or name == const.orb_name and qw.have_orb
end

function autopickup(item, name)
    if not qw.initialized or item.is_useless then
        return
    end

    reset_cached_turn_data()

    local class = item.class(true)
    if class == "gem" then
        return true
    elseif class == "rune" then
        record_seen_item(you.where(), item.name())
        return true
    elseif class == "orb" then
        record_seen_item(you.where(), item.name())
        c_persist.found_orb = true
        return goal_status == "Orb"
    end

    if equip_slot(item) then
        return not equip_is_dominated(item)
    elseif class == "gold" then
        return true
    elseif class == "potion" then
        return want_potion(item)
    elseif class == "scroll" then
        return want_scroll(item)
    elseif class == "wand" then
        return want_wand(item)
    elseif class == "missile" then
        return want_missile(item)
    elseif class == "misc" then
        return want_miscellaneous(item)
    else
        return false
    end
end

-----------------------------------------
-- item functions

function inventory_iter()
    return iter.invent_iterator:new(items.inventory())
end

function floor_item_iter()
    return iter.invent_iterator:new(you.floor_items())
end

-- Since DCSS 0.34, gear and consumables are stored in separate inventories:
-- 52 gear slots (weapons, missiles, armour, jewellery, staves, talismans, and
-- gizmos) and unlimited potions, scrolls, and other evokable items. Only gear
-- can fill up, so only it is counted here.
const.gear_classes = {
    ["weapon"] = true,
    ["missile"] = true,
    ["armour"] = true,
    ["jewellery"] = true,
    -- Staves report a terse class of "magical staff" (items.lua of crawl
    -- special-cases OBJ_STAVES in item_class_name), but we also include
    -- "staff" as a fallback in case that special case is removed.
    ["magical staff"] = true,
    ["staff"] = true,
    ["talisman"] = true,
    ["gizmo"] = true,
}

function free_inventory_slots()
    local slots = 52
    for item in inventory_iter() do
        if const.gear_classes[item.class(true)] then
            slots = slots - 1
        end
    end
    return max(slots, 0)
end

function item_letter(item)
    return items.index_to_letter(item.slot)
end

function get_item(letter)
    return items.inslot(items.letter_to_index(letter))
end

function find_item(cls, name)
    return turn_memo_args("find_item",
        function()
            for item in inventory_iter() do
                if item.class(true) == cls and item.name():find(name) then
                    return item
                end
            end
        end, cls, name)
end

function missile_damage(missile)
    if missile.class(true) ~= "missile"
            or missile:name():find("throwing net") then
        return
    end

    local damage = missile.damage
    if missile.ego() == "silver" then
        damage = damage * 7 / 6
    end

    return damage
end

function missile_quantity(missile)
    if missile.class(true) ~= "missile"
            or missile:name():find("throwing net") then
        return
    end

    return missile.quantity
end

function best_missile(value_func)
    return turn_memo_args("best_missile",
        function()
            local best_missile, best_value
            for item in inventory_iter() do
                local value = value_func(item)
                if value and (not best_value or value > best_value) then
                    best_missile = item
                    best_value = value
                end
            end
            return best_missile
        end, value_func)
end

function count_item(cls, name)
    local it = find_item(cls, name)
    if it then
        return it.quantity
    end

    return 0
end

function record_item_ident(item_type, item_subtype)
    if item_type == "potion" then
        c_persist.potion_ident[item_subtype] = true
    elseif item_type == "scroll" then
        c_persist.scroll_ident[item_subtype] = true
    end
end

function item_type_is_ided(item_type, subtype)
    if item_type == "potion" then
        return c_persist.potion_ident[subtype]
    elseif item_type == "scroll" then
        return c_persist.scroll_ident[subtype]
    end

    return false
end

function item_string(item)
    local name = item.name()
    local letter
    if item.slot then
        letter = item_letter(item)
    end
    return (letter and (letter .. " - ") or "") .. item.name()
        .. (item.equipped and " (equipped)" or "")
end

function c_choose_identify()
    local id_item = get_unidentified_item()
    if id_item then
        say("IDENTIFYING " .. id_item.name())
        return item_letter(id_item)
    end
end

function c_choose_brand_weapon()
    local weapon = get_brandable_weapon()
    if weapon then
        say("BRANDING " .. weapon:name() .. ".")
        return item_letter(weapon)
    end
end

function c_choose_enchant_weapon()
    local weapon = get_enchantable_weapon()
    if weapon then
        say("ENCHANTING " .. weapon:name() .. ".")
        return item_letter(weapon)
    end
end

function c_choose_enchant_armour()
    local armour = get_enchantable_armour()
    if armour then
        say("ENCHANTING " .. armour:name() .. ".")
        return item_letter(armour)
    end
end
function get_unidentified_item()
    local id_item
    for item in inventory_iter() do
        if item.class(true) == "potion"
                and not item.is_identified
                -- Prefer identifying potions over scrolls and prefer
                -- identifying smaller stacks.
                and (not id_item
                    or id_item.class(true) ~= "potion"
                    or item.quantity < id_item.quantity) then
            id_item = item
        elseif item.class(true) == "scroll"
                and not item.is_identified
                and (not id_item or id_item.class(true) ~= "potion")
                and (not id_item or item.quantity < id_item.quantity) then
            id_item = item
        end
    end

    return id_item
end
-- Coordinates and LOS

const.origin = { x = 0, y = 0 }

function supdist(pos)
    return max(abs(pos.x), abs(pos.y))
end

function feature_state(pos)
    if you.see_cell_solid_see(pos.x, pos.y) then
        return const.explore.reachable
    elseif you.see_cell_no_trans(pos.x, pos.y) then
        return const.explore.diggable
    end
    return const.explore.seen
end

function player_has_line_of_fire(target_pos, attack_id)
    local attack
    if attack_id then
        attack = get_attack(attack_id)
    else
        attack = get_ranged_attack()
    end

    if position_distance(const.origin, target_pos) > attack.range then
        return false
    end

    local positions = spells.path(attack.test_spell, target_pos.x,
        target_pos.y, 0, 0, false)
    for i, coords in ipairs(positions) do
        local pos = { x = coords[1], y = coords[2] }
        local hit_target = positions_equal(pos, target_pos)
        local mons = get_monster_at(pos)
        if not attack.is_penetrating
                and not hit_target
                and mons
                and not mons:ignores_player_projectiles() then
            return false
        end

        if mons and not mons:is_enemy()
                and not mons:is_harmless()
                and not mons:ignores_player_projectiles() then
            return false
        end

        if hit_target then
            return true
        end
    end

    return false
end

function positions_can_melee(from_pos, to_pos, range)
    local dist = position_distance(from_pos, to_pos)
    if dist == 0 then
        return false
    end

    if range == 1 then
        return dist == 1
    end

    if range == 3 then
        return dist <= 3 and cell_see_cell(from_pos, to_pos)
    end

    if range ~= 2 then
        return false
    end

    local x_diff = to_pos.x - from_pos.x
    local abs_x_diff = abs(x_diff)
    local y_diff = to_pos.y - from_pos.y
    local abs_y_diff = abs(y_diff)
    if abs_x_diff > abs_y_diff then
        local sign_diff = sign(x_diff)
        if abs_y_diff > 0 then
            return not is_solid_at({ x = from_pos.x + sign_diff,
                    y = from_pos.y }, true)
                -- We know that sign(y_diff) == y_diff.
                or not is_solid_at({ x = from_pos.x + sign_diff,
                    y = from_pos.y - y_diff }, true)
        else
            return not is_solid_at({ x = from_pos.x + sign_diff,
                y = from_pos.y }, true)
        end

    elseif abs_x_diff < abs_y_diff then
        local sign_diff = sign(y_diff)
        if abs_x_diff > 0 then
            return not is_solid_at({ x = from_pos.x,
                    y = from_pos.y + sign_diff }, true)
                or not is_solid_at({ x = from_pos.x - x_diff,
                    y = from_pos.y + sign_diff }, true)
        else
            return not is_solid_at({ x = from_pos.x,
                y = from_pos.y + sign_diff }, true)
        end
    else
        return not is_solid_at({ x = from_pos.x + sign(x_diff),
            y = from_pos.y + sign(y_diff) }, true)
    end
end

function square_iter(pos, radius, include_center)
    if not radius then
        radius = qw.los_radius
    end
    if radius <= 0 then
        error("Radius must be a positive integer.")
    end

    local dx = -radius
    local dy = -radius - 1
    return function()
        if dy == radius then
            if dx == radius then
                return
            else
                dx = dx + 1
                dy = -radius
            end
        else
            dy = dy + 1
            if not include_center and dx == 0 and dy == 0 then
                dy = dy + 1
            end
        end

        return { x = pos.x + dx, y = pos.y + dy }
    end
end

function adjacent_iter(pos, include_center)
    return square_iter(pos, 1, include_center)
end


local square = {
    {1, -1}, {1, 1}, {-1, 1}, {-1, -1}
}

local square_move = {
    {0, 1}, {-1, 0}, {0, -1}, {1, 0}
}

function radius_iter(pos, radius, include_center)
    if not radius then
        radius = qw.los_radius
    end
    assert(radius > 0, "Radius must be a positive integer.")

    local r = 0
    local i = 1
    local dx, dy = 0, 0
    return function()
        if r == 0 then
            r = 1
            if include_center then
                return pos
            end
        end

        local last_point = i == #square + 1
        if last_point
                and dx + square_move[i - 1][1] == r * square[1][1]
                and dy + square_move[i - 1][2] == r * square[1][2]
            or not last_point
                and dx == r * square[i][1]
                and dy == r * square[i][2] then

            if last_point then
                r = r + 1
                if r > radius then
                    return
                end

                i = 1
            else
                i = i + 1
            end
        end

        if i == 1 then
            dx = r * square[1][1]
            dy = r * square[1][2]
        else
            dx = dx + square_move[i - 1][1]
            dy = dy + square_move[i - 1][2]
        end

        return { x = pos.x + dx, y = pos.y + dy }
    end
end

function hash_position(pos)
    return 2 * const.gxm * pos.x + pos.y
end

function unhash_position(hash)
    local x = math.floor(hash / (2 * const.gxm) + 0.5)
    return { x = x, y = hash - 2 * const.gxm * x }
end

function is_adjacent(pos, center)
    if not center then
        center = const.origin
    end

    return max(abs(pos.x - center.x), abs(pos.y - center.y)) == 1
end

function position_distance(a, b)
    return supdist(position_difference(a, b))
end

function position_difference(a, b)
    return { x = a.x - b.x, y = a.y - b.y }
end

function position_sum(a, b)
    return { x = a.x + b.x, y = a.y + b.y }
end

function positions_equal(a, b)
    return a.x == b.x and a.y == b.y
end

function position_is_origin(a)
    return a.x == 0 and a.y == 0
end

function cell_see_cell(a, b)
    return position_distance(a, b) <= qw.los_radius
        and view.cell_see_cell(a.x, a.y, b.x, b.y)
end
---------------------------------------------
-- ready function and main coroutine

function stop()
    qw.automatic = false
    unset_options()
end

function start()
    qw.automatic = true
    set_options()
    ready()
end

function startstop()
    if qw.automatic then
        stop()
    else
        start()
    end
end

function panic(msg)
    crawl.mpr("<lightred>" .. msg .. "</lightred>")
    stop()
end

function set_options()
    crawl.setopt("pickup_mode = multi")
    crawl.setopt("message_colour += mute:Search for what")
    crawl.setopt("message_colour += mute:Can't find anything")
    crawl.setopt("message_colour += mute:Drop what")
    crawl.setopt("message_colour += mute:Okay. then")
    crawl.setopt("message_colour += mute:Use which ability")
    crawl.setopt("message_colour += mute:Read which item")
    crawl.setopt("message_colour += mute:Drink which item")
    crawl.setopt("message_colour += mute:not good enough")
    crawl.setopt("message_colour += mute:Attack whom")
    crawl.setopt("message_colour += mute:move target cursor")
    crawl.setopt("message_colour += mute:Aim:")
    crawl.setopt("message_colour += mute:You reach to attack")
    crawl.enable_more(false)
end

function unset_options()
    crawl.setopt("pickup_mode = auto")
    crawl.setopt("message_colour -= mute:Search for what")
    crawl.setopt("message_colour -= mute:Can't find anything")
    crawl.setopt("message_colour -= mute:Drop what")
    crawl.setopt("message_colour -= mute:Okay. then")
    crawl.setopt("message_colour -= mute:Use which ability")
    crawl.setopt("message_colour -= mute:Read which item")
    crawl.setopt("message_colour -= mute:Drink which item")
    crawl.setopt("message_colour -= mute:not good enough")
    crawl.setopt("message_colour -= mute:Attack whom")
    crawl.setopt("message_colour -= mute:move target cursor")
    crawl.setopt("message_colour -= mute:Aim:")
    crawl.setopt("message_colour -= mute:You reach to attack")
    crawl.enable_more(true)
end

function qw_main()
    turn_update()

    if qw.time_passed and qw.single_step then
        stop()
    end

    local did_restart = qw.restart_cascade
    if qw.automatic then
        crawl.flush_input()
        crawl.more_autoclear(true)
        if qw.have_message then
            plan_message()
        else
            plans.turn()
        end
    end
    -- restart_cascade must remain true for the entire move cascade while we're
    -- restarting.
    if did_restart then
        qw.restart_cascade = false
    end
end

function run_qw()
    if qw.abort then
        return
    end

    if qw.update_coroutine == nil then
        qw.update_coroutine = coroutine.create(qw_main)
    end

    local okay, err = coroutine.resume(qw.update_coroutine)
    if not okay then
        error("Error in coroutine: " .. err)
        qw.abort = true
    end

    if coroutine.status(qw.update_coroutine) == "dead" then
        qw.update_coroutine = nil
        qw.do_dummy_action = qw.do_dummy_action == nil and qw.restart_cascade
    else
        qw.do_dummy_action = qw.do_dummy_action == nil
    end

    local memory_count = collectgarbage("count")
    if debug_channel("throttle") and qw.throttle then
        dsay("Memory count is " .. tostring(memory_count))
    end

    if qw.max_memory and memory_count > qw.max_memory then
        collectgarbage("collect")

        if collectgarbage("count") > qw.max_memory then
            qw.abort = true
            dsay("Memory usage above " .. tostring(qw.max_memory))
            dsay("Aborting...")
            return
        end
    end
    qw.throttle = false

    if qw.do_dummy_action then
        crawl.process_keys(":" .. string.char(27) .. string.char(27))
    end
    qw.do_dummy_action = nil
end

function ready()
    run_qw()
end

function hit_closest()
    startstop()
end
------------------
-- Level map data processing

-- Maximum map width. We use this as a general map radius that's guaranteed to
-- reach the entire map, since qw is never given absolute coordinates by crawl.
const.gxm = 80

-- Autoexplore state enum.
const.autoexplore = {
    "needed",
    "partial",
    "transporter",
    "runed_door",
    "full",
}

const.map_select = {
    "none",
    "excluded",
    "main",
    "both",
}

function main_map_selected(map_select)
    return map_select == const.map_select.main
        or map_select == const.map_select.both
end

function excluded_map_selected(map_select)
    return map_select == const.map_select.excluded
        or map_select == const.map_select.both
end

function update_waypoint(new_level)
    local place = where
    if in_portal() then
        place = "Portal"
    end

    local new_waypoint = false
    local waypoint_num = c_persist.waypoints[place]
    -- XXX: Hack to make Tomb hatch plans work. Re-create the waypoint each
    -- time we enter a level.
    if new_level and waypoint_num and in_branch("Tomb") then
        travel.set_waypoint(waypoint_num, 0, 0)
        new_waypoint = true
    elseif not waypoint_num then
        waypoint_num = c_persist.waypoint_count
        c_persist.waypoints[place] = waypoint_num
        c_persist.waypoint_count = waypoint_num + 1
        travel.set_waypoint(waypoint_num, 0, 0)
        new_waypoint = true
    end

    if not qw.map_pos then
        qw.map_pos = {}
    end
    qw.map_pos.x, qw.map_pos.y = travel.waypoint_delta(waypoint_num)

    -- The waypoint can become invalid due to entering a new Portal, a new Pan
    -- level, or due to an Abyss shift, etc.
    if not qw.map_pos.x then
        travel.set_waypoint(waypoint_num, 0, 0)
        qw.map_pos.x, qw.map_pos.y = travel.waypoint_delta(waypoint_num)
        new_waypoint = true
    end

    if new_level or new_waypoint then
        qw.move_destination = nil
        qw.enemy_map_memory = nil
        qw.last_enemy_map_memory = nil
    end

    return new_waypoint
end

function record_map_mode_search(key, start_hash, count, end_hash)
    if not map_mode_searches[key] then
        map_mode_searches[key] = {}
    end

    if not map_mode_searches[key][start_hash] then
        map_mode_searches[key][start_hash]  = {}
    end

    map_mode_searches[key][start_hash][count] = end_hash
end

function clear_map_cache(parity, full_clear)
    if debug_channel("map") then
        dsay((full_clear and "Full clearing" or "Clearing")
            .. " map cache for slot " .. tostring(parity))
    end

    if full_clear then
        map_mode_searches_cache[parity] = {}
    end

    feature_map_positions_cache[parity] = {}
    item_map_positions_cache[parity] = {}
    distance_maps_cache[parity] = {}

    traversal_maps_cache[parity] = {}
    for x = -const.gxm, const.gxm do
        traversal_maps_cache[parity][x] = {}
    end

    exclusion_maps_cache[parity] = {}
    for x = -const.gxm, const.gxm do
        exclusion_maps_cache[parity][x] = {}
    end

    adjacent_floor_maps_cache[parity] = {}
    for x = -const.gxm, const.gxm do
        adjacent_floor_maps_cache[parity][x] = {}
    end
end

function find_features(feats, radius)
    if not radius then
        radius = const.gxm
    end

    local searches = {}
    for _, feat in ipairs(feats) do
        searches[feat] = true
    end

    local positions = {}
    local found_feats = {}
    local i = 1
    for pos in square_iter(const.origin, radius, true) do
        if qw.coroutine_throttle and i % 1000 == 0 then
            if debug_channel("throttle") then
                dsay("Searched features in block " .. tostring(i / 1000)
                    .. " of map positions")
            end

            qw.throttle = true
            coroutine.yield()
        end

        local feat = view.feature_at(pos.x, pos.y)
        if searches[feat] then
            if not feature_map_positions[feat] then
                feature_map_positions[feat] = {}
            end

            local gpos = position_sum(qw.map_pos, pos)
            local hash = hash_position(gpos)
            if not feature_map_positions[feat][hash] then
                feature_map_positions[feat][hash] = gpos
            end
            table.insert(positions, gpos)
            table.insert(found_feats, feat)
        end

        i = i + 1
    end

    return positions, found_feats
end

function find_map_items(item_names, radius)
    if not radius then
        radius = const.gxm
    end

    local searches = {}
    for _, name in ipairs(item_names) do
        searches[name] = true
    end

    local positions = {}
    local found_items = {}
    local i = 1
    for pos in square_iter(const.origin, radius, true) do
        if qw.coroutine_throttle and i % 1000 == 0 then
            if debug_channel("throttle") then
                dsay("Searched items in block " .. tostring(i / 1000)
                    .. " of map positions")
            end

            qw.throttle = true
            coroutine.yield()
        end

        local floor_items = items.get_items_at(pos.x, pos.y)
        if floor_items then
            for _, it in ipairs(floor_items) do
                local name = it.name()
                if searches[name] then
                    local map_pos = position_sum(qw.map_pos, pos)
                    item_map_positions[name] = map_pos
                    table.insert(positions, map_pos)
                    table.insert(found_items, name)

                    searches[name] = nil
                    if table_is_empty(searches) then
                        return positions, found_items
                    end
                end
            end
        end

        i = i + 1
    end

    return positions, found_items
end

function distance_map_remove(dist_map)
    if debug_channel("map") then
        dsay("Removing " .. (permanent and "permanent" or "temporary")
            .. " distance map at "
            .. cell_string_from_map_position(dist_map.pos))
    end

    dist_map.map = nil
    dist_map.excluded_map = nil
    distance_maps[dist_map.hash] = nil
end

function distance_map_initialize_maps(dist_map, excluded_only)
    if not excluded_only then
        dist_map.map = {}
        for x = -const.gxm, const.gxm do
            dist_map.map[x] = {}
        end
        dist_map.map[dist_map.pos.x][dist_map.pos.y] = 0
    end

    dist_map.excluded_map = {}
    for x = -const.gxm, const.gxm do
        dist_map.excluded_map[x] = {}
    end
    dist_map.excluded_map[dist_map.pos.x][dist_map.pos.y] =
        map_is_unexcluded_at(dist_map.pos) and 0 or nil
end

function distance_map_initialize(pos, permanent, radius)
    if permanent == nil then
        permanent = false
    end

    if debug_channel("map") then
        dsay("Creating " .. (permanent and "permanent" or "temporary")
            .. " distance map at "
            .. cell_string_from_map_position(pos))
    end

    local dist_map = {}

    dist_map.pos = util.copy_table(pos)
    dist_map.hash = hash_position(pos)
    dist_map.permanent = permanent
    dist_map.radius = radius

    distance_map_initialize_maps(dist_map)
    local dest_pos = new_update_position(pos)
    dist_map.queue = { dest_pos }
    return dist_map
end

function is_traversable_at(pos)
    local gpos = position_sum(qw.map_pos, pos)
    return traversal_map[gpos.x][gpos.y]
end

function map_is_traversable_at(pos)
    return traversal_map[pos.x][pos.y]
end

function map_is_unseen_at(pos)
    return traversal_map[pos.x][pos.y] == nil
end

function distance_map_adjacent_dist(pos, dist_map, map_select)
    local best_dist, best_excluded_dist
    local main_selected = main_map_selected(map_select)
    local excluded_selected = excluded_map_selected(map_select)
    for pos in adjacent_iter(pos) do
        if map_is_traversable_at(pos) then
            local dist
            if main_selected then
                dist = dist_map.map[pos.x][pos.y]
                if dist and (not best_dist or best_dist > dist) then
                    best_dist = dist
                end
            end

            if excluded_selected then
                dist = dist_map.excluded_map[pos.x][pos.y]
                if map_is_unexcluded_at(pos)
                        and dist
                        and (not best_excluded_dist
                            or best_excluded_dist > dist) then
                    best_excluded_dist = dist
                end
            end
        end
    end
    if main_selected then
        return best_dist, best_excluded_dist
    else
        return best_excluded_dist
    end
end

function distance_map_update_adjacent_pos(pos, center, dist_map)
    if positions_equal(pos, dist_map.pos)
            or (dist_map.radius
                    and position_distance(pos, dist_map.pos) > dist_map.radius)
            -- Untraversable cells don't need distance map updates.
            or not map_is_traversable_at(pos) then
        return
    end

    local update_pos
    local center_dist = dist_map.map[center.x][center.y]
    local dist = dist_map.map[pos.x][pos.y]
    if not center.excluded_only
            and center_dist
            and (not dist or dist > center_dist + 1) then
        dist_map.map[pos.x][pos.y] = center_dist + 1

        update_pos = new_update_position(pos)
    end

    center_dist = dist_map.excluded_map[center.x][center.y]
    dist = dist_map.excluded_map[pos.x][pos.y]
    if map_is_unexcluded_at(pos)
            and center_dist
            and (not dist or dist > center_dist + 1) then
        dist_map.excluded_map[pos.x][pos.y] = center_dist + 1

        if not update_pos then
            update_pos = new_update_position(pos)
            update_pos.excluded_only = true
        end
    end

    if update_pos then
        table.insert(dist_map.queue, update_pos)
    end
end

function distance_map_propagate(dist_map)
    if #dist_map.queue == 0 then
        return
    end

    if debug_channel("map") then
        dsay("Propagating distance map at "
            .. cell_string_from_map_position(dist_map.pos)
            .. " with " .. tostring(#dist_map.queue) .. " update positions")
    end

    local ind = 1
    local count = ind
    while ind <= #dist_map.queue do
        if qw.coroutine_throttle and count % 300 == 0 then
            if debug_channel("throttle") then
                dsay("Propagated block " .. tostring(count / 300)
                    .. " with " .. tostring(#dist_map.queue - ind)
                    .. " positions remaining")
            end

            qw.throttle = true
            coroutine.yield()
        end

        local center = dist_map.queue[ind]
        for pos in adjacent_iter(center) do
            distance_map_update_adjacent_pos(pos, center, dist_map)
        end

        ind = ind + 1
        count = ind
    end

    dist_map.queue = {}
end

function handle_item_searches(cell)
    -- Don't do an expensive iteration over all items if we don't have an
    -- active search.
    if table_is_empty(item_searches) then
        return
    end

    local floor_items = items.get_items_at(cell.los_pos.x, cell.los_pos.y)
    if not floor_items then
        return
    end

    for _, it in ipairs(floor_items) do
        local name = it.name()
        if item_searches[name] then
            item_map_positions[name] = cell.pos
            item_searches[name] = nil

            if table_is_empty(item_searches) then
                return
            end
        end
    end
end

function new_update_position(pos)
    return {
        x = pos.x,
        y = pos.y,
        hash = hash_position(pos),
        excluded_only = false,
    }
end

function distance_map_update_position(pos, dist_map, map_select)
    if dist_map.radius
            and position_distance(dist_map.pos, pos) > dist_map.radius then
        return
    end

    local traversable = map_is_traversable_at(pos)
    local dist, excluded_dist, update_pos
    local have_adjacent = false
    -- If we're traversable and don't have a map distance, we just became
    -- traversable, so update the map distance from adjacent squares.
    if main_map_selected(map_select)
            and traversable
            and not dist_map.map[pos.x][pos.y] then
        dist, excluded_dist = distance_map_adjacent_dist(pos, dist_map,
            map_select)
        have_adjacent = true
        if dist then
            dist_map.map[pos.x][pos.y] = dist + 1
            update_pos = new_update_position(pos)
        end
    end

    -- We're traversable and not excluded, yet have no excluded distance.
    if excluded_map_selected(map_select)
            and traversable
            and map_is_unexcluded_at(pos)
            and not dist_map.excluded_map[pos.x][pos.y] then
        if not have_adjacent then
            excluded_dist = distance_map_adjacent_dist(pos, dist_map,
                const.map_select.excluded)
        end

        if excluded_dist then
            dist_map.excluded_map[pos.x][pos.y] = excluded_dist + 1
            if not update_pos then
                update_pos = new_update_position(pos)
                update_pos.excluded_only = true
            end
        end
    end

    if update_pos then
        table.insert(dist_map.queue, update_pos)
    end
end

function has_exclusion_center_at(pos)
    local hash = hash_position(position_sum(qw.map_pos, pos))
    return c_persist.exclusions[where] and c_persist.exclusions[where][hash]
end

--[[
Are the given map coordinates unexcluded according to the exclusion map cache?
@table pos The map position.
@treturn boolean True if coordinates are unexcluded, false otherwise.
--]]
function map_is_unexcluded_at(pos)
    return exclusion_map[pos.x][pos.y]
end

function unexcluded_at(pos)
    return map_is_unexcluded_at(position_sum(qw.map_pos, pos))
end

function update_feature(branch, depth, feat, hash, state)
    local dir, num = stone_stairs_type(feat)
    if dir then
        update_stone_stairs(branch, depth, dir, num, state)
        return
    end

    if feat == "abyssal_stair" then
        update_abyssal_stairs(hash, state)
        return
    end

    local dest_branch, dir = branch_stairs_type(feat)
    if dest_branch then
        update_branch_stairs(branch, depth, dest_branch, dir, state)
        return
    end

    local dir = escape_hatch_type(feat)
    if dir then
        update_escape_hatch(branch, depth, dir, hash, state)
        return
    end

    if feat == "transit_pandemonium" then
        update_pan_transit(hash, state)
        return
    end

    local god = altar_god(feat)
    if god then
        update_altar(god, make_level(branch, depth), hash, state)
        return
    end
end

local state_features = {}
function feature_has_map_state(feat)
    local has_state = state_features[feat]
    if has_state == nil then
        has_state = stone_stairs_type(feat)
            or feat == "abyssal_stair"
            or branch_stairs_type(feat)
            or escape_hatch_type(feat)
            or feat == "transit_pandemonium"
            or altar_god(feat)
        state_features[feat] = has_state
    end

    return has_state
end

function expire_cell_portal(cell)
    for feat, positions in pairs(feature_map_positions) do
        local branch = branch_stairs_type(feat)
        if branch and is_portal_branch(branch) then
            for hash, _ in pairs(positions) do
                if cell.hash == hash then
                    remove_portal(where, branch)
                    return
                end
            end
        end
    end
end

function update_cell_feature(cell)
    if cell.feat == "expired_portal" then
        expire_cell_portal(cell)
    elseif not qw.have_slimy_walls and cell.feat == "slimy_wall" then
        qw.have_slimy_walls = true
    end

    local has_state = feature_has_map_state(cell.feat)
    if cell.feat == "runelight" or has_state then
        if not feature_map_positions[cell.feat] then
            feature_map_positions[cell.feat] = {}
        end
        if not feature_map_positions[cell.feat][cell.hash] then
            feature_map_positions[cell.feat][cell.hash] = cell.pos
        end
    end

    if not has_state then
        return
    end

    local enemies = assess_enemies(const.duration.ignore)
    local feat_state = feature_state(cell.los_pos)
    update_feature(where_branch, where_depth, cell.feat, cell.hash,
        { safe = exclusion_map[cell.pos.x][cell.pos.y], feat = feat_state,
            threat = enemies.threat })

    if feat_state < const.explore.reachable then
        check_reachable_features[cell.feat] = true
    end
end

function update_map_at_cell(cell, queue, seen)
    local map_reset = const.map_select.none

    if seen[cell.hash] then
        return map_reset
    end

    local map_updated = false
    local old_traversable = traversal_map[cell.pos.x][cell.pos.y]
    local cur_traversable = feature_is_traversable(cell.feat)
    if old_traversable ~= cur_traversable then
        traversal_map[cell.pos.x][cell.pos.y] = cur_traversable
        -- A cell went from traversable to untraversable, so any distance maps
        -- need a full reset.
        if old_traversable and not cur_traversable then
            map_reset = const.map_select.both
        end
        map_updated = true
    end

    local old_unexcluded = exclusion_map[cell.pos.x][cell.pos.y]
    local cur_unexcluded =
        not (view.in_known_map_bounds(cell.los_pos.x, cell.los_pos.y)
            and travel.is_excluded(cell.los_pos.x, cell.los_pos.y))
    if cur_traversable and old_unexcluded ~= cur_unexcluded then
        exclusion_map[cell.pos.x][cell.pos.y] = cur_unexcluded
        -- A traversable cell went from unexcluded to excluded, so the excluded
        -- maps of all distance maps need a reset.
        if old_unexcluded
                and not unexcluded
                and map_reset < const.map_select.both then
            map_reset = const.map_select.excluded
        end
        map_updated = true
    end

    update_cell_feature(cell)
    seen[cell.hash] = true

    if not map_updated then
        return map_reset
    end

    for pos in adjacent_iter(cell.los_pos) do
        local acell = cell_from_position(pos, true)
        if acell and not seen[acell.hash] then
            table.insert(queue, acell)
        end
    end

    return map_reset
end

function update_map_cells()
    local queue = {}
    for pos in square_iter(const.origin, qw.los_radius, true) do
        local cell = cell_from_position(pos, true)
        if cell then
            table.insert(queue, cell)
        end
    end

    local seen = {}
    local ind = 1
    local count = 1
    local map_reset = const.map_select.none
    while ind <= #queue do
        if qw.coroutine_throttle and count % 1000 == 0 then
            if debug_channel("throttle") then
                dsay("Updated map in block " .. tostring(count / 1000)
                    .. " with " .. tostring(#queue - ind) .. " cells remaining")
            end

            qw.throttle = true
            coroutine.yield()
        end

        local cell = queue[ind]
        local cell_map_reset = update_map_at_cell(cell, queue, seen)
        if cell_map_reset > map_reset then
            map_reset = cell_map_reset
        end

        handle_item_searches(cell)

        count = ind
        ind = ind + 1
    end

    return queue, map_reset
end

function update_distance_maps_at_cells(queue, map_select)
    for i, cell in ipairs(queue) do
        if qw.coroutine_throttle and i % 1000 == 0 then
            if debug_channel("throttle") then
                dsay("Updated distance maps in block " .. tostring(i / 1000)
                    .. " with " .. tostring(#queue - i) .. " cells remaining")
            end

            qw.throttle = true
            coroutine.yield()
        end

        for _, dist_map in pairs(distance_maps) do
            distance_map_update_position(cell.pos, dist_map, map_select)
        end
    end
end

function reset_c_persist(new_waypoint, new_level)
    -- A new waypoint means certain features that need to be identified by
    -- their global coordinates have to be erased.
    if new_waypoint then
        c_persist.up_hatches[where] = nil
        c_persist.down_hatches[where] = nil

        for god, _ in pairs(c_persist.altars) do
            c_persist.altars[god][where] = nil
        end
    end

    if new_waypoint and branch_is_temporary(where_branch) then
        c_persist.autoexplore[where_branch] = const.autoexplore.needed
        c_persist.branch_exits[where_branch] = {}
    end

    -- Certain branches and portals like Bazaars can be entered multiple times,
    -- so we need to clear their data immediately after leaving.
    if new_level then
        prev_branch = parse_level_range(previous_where)
        if prev_branch and branch_is_temporary(prev_branch) then
            c_persist.autoexplore[prev_branch] = const.autoexplore.needed
            c_persist.branch_exits[prev_branch] = {}
        end
    end

    if in_branch("Abyss") then
        if new_waypoint then
            c_persist.abyssal_stairs = {}
        end

        if new_level then
            c_persist.sense_abyssal_rune = false
        end
    end

    if new_waypoint and in_branch("Pan") then
        c_persist.pan_transits = {}
    end
end

function reset_map_cache(new_level, full_clear, new_waypoint)
    if new_waypoint or full_clear then
        clear_map_cache(cache_parity, full_clear)
    end

    if not previous_where or new_level or new_waypoint or full_clear then
        traversal_map = traversal_maps_cache[cache_parity]
        exclusion_map = exclusion_maps_cache[cache_parity]
        adjacent_floor_map = adjacent_floor_maps_cache[cache_parity]
        distance_maps = distance_maps_cache[cache_parity]
        feature_map_positions = feature_map_positions_cache[cache_parity]
        item_map_positions = item_map_positions_cache[cache_parity]
        map_mode_searches = map_mode_searches_cache[cache_parity]
    end
end

function reset_item_tracking()
    if in_branch("Abyss") then
        local rune = branch_runes(where_branch, true)[1]
        if not (c_persist.seen_items[where]
                    and c_persist.seen_items[where][rune])
                and not c_persist.sense_abyssal_rune then
            item_map_positions[rune] = nil
        end
    end

    item_searches = {}
    if c_persist.seen_items[where] then
        for name, _ in pairs(c_persist.seen_items[where]) do
            if not item_map_positions[name] then
                item_searches[name] = true
            end
        end
    end

    local purged = {}
    for name, _ in pairs(item_map_positions) do
        if have_quest_item(name) then
            table.insert(purged, name)
        end
    end
    for name, _ in ipairs(purged) do
        item_map_positions[name] = nil
    end
end

function update_distance_maps(queue, reset)
    local removed_maps = {}
    for _, dist_map in pairs(distance_maps) do
        if not map_is_traversable_at(dist_map.pos) then
            table.insert(removed_maps, dist_map)
        end
    end
    for _, dist_map in ipairs(removed_maps) do
        distance_map_remove(dist_map)
    end

    local excluded_only = reset == const.map_select.excluded
    if reset > const.map_select.none then
        if debug_channel("map") then
            dsay("Resetting "
                .. (excluded_only and "excluded map" or "both maps")
                .. " for all distance maps")
        end

        for hash, dist_map in pairs(distance_maps) do
            distance_map_initialize_maps(dist_map, excluded_only)
            local pos = new_update_position(dist_map.pos)
            pos.excluded_only = excluded_only
            dist_map.queue = { pos }
        end
    end

    if reset < const.map_select.both then
        update_distance_maps_at_cells(queue,
            reset == const.map_select.none and const.map_select.both
                or const.map_select.main)
    end

    for _, dist_map in pairs(distance_maps) do
        distance_map_propagate(dist_map)
    end
end

function update_seen_items()
    if not c_persist.seen_items[where] then
        return
    end

    -- Any seen item for which we don't have an item position is unregistered.
    local seen_items = {}
    for name, _ in pairs(c_persist.seen_items[where]) do
        if item_map_positions[name] then
            seen_items[name] = true
        end
    end
    c_persist.seen_items[where] = seen_items
end

function update_map_mode_search()
    if not map_mode_search_key then
        return
    end

    local feat = view.feature_at(0, 0)
    -- We assume we've landed on the next feature in our current "X<key>"
    -- cycle because the feature at our position uses that key.
    if feature_uses_map_key(map_mode_search_key, feat) then
        record_map_mode_search(map_mode_search_key, map_mode_search_hash,
            map_mode_search_count, hash_position(qw.map_pos))
    end
    map_mode_search_key = nil
    map_mode_search_hash = nil
    map_mode_search_count = nil
end

function update_adjacent_floor(queue)
    for _, cell in ipairs(queue) do
        if map_is_traversable_at(cell.pos) then
            local floor_count = 0
            for pos in adjacent_iter(cell.los_pos) do
                if not is_solid_at(pos, true) then
                    floor_count = floor_count + 1
                end
            end
            adjacent_floor_map[cell.pos.x][cell.pos.y] = floor_count
        end
    end
end

function update_map(new_level, full_clear)
    local new_waypoint = update_waypoint(new_level)

    reset_c_persist(new_waypoint, new_level)
    reset_map_cache(new_level, full_clear, new_waypoint)
    reset_item_tracking()

    update_exclusions(new_waypoint)

    if new_level then
        qw.have_slimy_walls = false
    end

    local cell_queue, map_reset = update_map_cells()
    update_adjacent_floor(cell_queue)

    update_seen_items()

    update_distance_maps(cell_queue, map_reset)

    update_map_mode_search()
    update_transporters()
end

function cell_from_position(pos, no_unseen)
    local feat = view.feature_at(pos.x, pos.y)
    if no_unseen and feat == "unseen" then
        return
    end

    local cell = {}
    cell.los_pos = pos
    cell.feat = feat
    cell.pos = position_sum(qw.map_pos, pos)
    cell.hash = hash_position(cell.pos)
    return cell
end

function get_distance_map(pos, permanent, radius)
    local hash = hash_position(pos)
    if not distance_maps[hash] then
        distance_maps[hash] = distance_map_initialize(pos, permanent, radius)
        distance_map_propagate(distance_maps[hash])
    end
    return distance_maps[hash]
end

function get_feature_map_positions(feats)
    local positions = {}
    local features = {}
    for _, feat in ipairs(feats) do
        if feature_map_positions[feat] then
            for _, pos in pairs(feature_map_positions[feat]) do
                table.insert(positions, pos)
                table.insert(features, feat)
            end
        end
    end
    if #positions > 0 then
        return positions, features
    end
end

function get_item_map_positions(item_names, radius)
    local positions = {}
    local found_items = {}
    for _, name in ipairs(item_names) do
        if item_map_positions[name] then
            table.insert(positions, item_map_positions[name])
            table.insert(found_items, name)
        end
    end
    if #positions > 0 then
        return positions, found_items
    end

    positions, found_items = find_map_items(item_names, radius)

    -- If we've searched the map for the abyssal rune and not found it, unset
    -- our sensing of the rune.
    if in_branch("Abyss") then
        local rune = branch_runes(where_branch, true)[1]
        if util.contains(item_names, rune)
                and not util.contains(found_items, rune) then
            c_persist.sense_abyssal_rune = false
        end
    end

    if #positions > 0 then
        return positions, found_items
    end
end

function remove_exclusions(record_only)
    if record_only or not c_persist.exclusions[where] then
        c_persist.exclusions[where] = nil
        return
    end

    for hash, _ in pairs(c_persist.exclusions[where]) do
        local pos = position_difference(unhash_position(hash), qw.map_pos)
        if view.in_known_map_bounds(pos.x, pos.y) then
            if debug_channel("combat") then
                dsay("Unexcluding position "
                    .. cell_string_from_map_position(pos))
            end

            travel.del_exclude(pos.x, pos.y)
        elseif debug_channel("combat") then
            dsay("Ignoring out of bounds exclusion coordinates "
                .. pos_string(pos))
        end
    end
    c_persist.exclusions[where] = nil
end

function exclude_position(pos)
    if debug_channel("map") then
        local desc
        local mons = get_monster_at(pos)
        if mons then
            desc = mons:name()
        else
            desc = view.feature_at(pos.x, pos.y)
        end
        dsay("Excluding " .. desc .. " at " .. pos_string(pos))
    end

    local hash = hash_position(position_sum(qw.map_pos, pos))
    if not c_persist.exclusions[where] then
        c_persist.exclusions[where] = {}
    end
    c_persist.exclusions[where][hash] = true

    travel.set_exclude(pos.x, pos.y)
end

function level_has_exclusions(branch, depth)
    return c_persist.exclusions[make_level(branch, depth)]
end

function update_exclusions(new_waypoint)
    if new_waypoint then
        remove_exclusions()
    end

    -- We're unlikely to be able to run away when mesmerised.
    if you.mesmerised() then
        return
    end

    -- Monsters we can't reach via melee or ranged attack that also can't move
    -- to our melee range get excluded immediately.
    local auto_exclude = {}
    local ranged_attack = get_ranged_attack()
    for _, enemy in ipairs(qw.enemy_list) do
        if not has_exclusion_center_at(enemy:pos())
                -- No excluding safe monsters.
                and not enemy:is_safe()
                -- No excluding temporary monsters.
                and not enemy:is_summoned()
                -- We need to at least see all cells adjacent to them to be
                -- so our movement evaluation is reasonably correct.
                and enemy:adjacent_cells_known()
                -- We can't move into melee range...
                and not enemy:player_has_path_to_melee()
                -- ... they can't move to where we could melee them
                and not enemy:player_can_wait_for_melee()
                -- ... and we can't target them with a ranged attack
                and not (ranged_attack
                    and enemy:player_has_line_of_fire(ranged_attack.index))
                -- ... and we know that we don't want to dig them out.
                and not enemy:should_dig_unreachable() then
            table.insert(auto_exclude, enemy:pos())
        end
    end
    if #auto_exclude > 0 then
        for _, pos in ipairs(auto_exclude) do
            exclude_position(pos)
        end
        return
    end

    -- We potentially exclude monsters that can't reach our position when we've
    -- tried to fight them from full HP. To make this assessment, we track the
    -- last turn a monster could reach us.
    for _, enemy in ipairs(qw.enemy_list) do
        if not enemy:is_summoned() and enemy:has_path_to_player() then
            qw.incoming_monsters_turn = you.turns()
            return
        end
    end

    -- If we've been trying to attack monsters that can't reach our position
    -- and get to low HP, we wan't to exclude them and end the fight. We
    -- additionally require that we've been at full HP since the last turn were
    -- we had incoming monsters. This way if we fight a mix of some monsters
    -- that can reach us and some that can't, we'll deal with the monsters that
    -- can't only after finishing off the monsters that can and then resting to
    -- full HP.
    if qw.full_hp_turn > 0
            and qw.full_hp_turn >= qw.incoming_monsters_turn
            and hp_is_low(50) then
        for _, enemy in ipairs(qw.enemy_list) do
            if not enemy:is_summoned() then
                exclude_position(enemy:pos())
            end
        end
    end
end

function want_to_use_transporters()
    return c_persist.autoexplore[where] == const.autoexplore.transporter
        and (in_branch("Temple") or in_portal())
end

function update_transporters()
    transp_search = nil
    if want_to_use_transporters() then
        local feat = view.feature_at(0, 0)
        if feature_uses_map_key(">", feat) and transp_search_zone then
            if not transp_map[transp_search_zone] then
                transp_map[transp_search_zone] = {}
            end
            transp_map[transp_search_zone][transp_search_count] = transp_zone
            transp_search_zone = nil
            transp_search_count = nil
            if feat == "transporter" then
                transp_search = transp_zone
            end
        elseif branch_exit(where_branch) then
            transp_zone = 0
            transp_orient = false
        end
    end
end
-----------------------------------------
-- The Monster class

util.defclass("Monster")

function Monster:new(mons)
    local monster = {}
    setmetatable(monster, self)
    monster.minfo = mons
    monster.props = {}
    return monster
end

function Monster:property_memo(name, func)
    if self.props[name] == nil then
        local val
        if func then
            val = func()
        else
            val = self.minfo[name](self.minfo)
        end

        if val == nil then
            val = false
        end
        self.props[name] = val
    end

    return self.props[name]
end

function Monster:property_memo_args(name, func, ...)
    -- Note: crawl uses Lua 5.4 as of DCSS 0.34, so we use select() instead of
    -- the removed Lua 5.1-style implicit arg table.
    local num_args = select('#', ...)
    assert(num_args > 0)

    local parent, key
    for j = 1, num_args do
        if j == 1 then
            parent = self.props
            key = name
        end

        if parent[key] == nil then
            parent[key] = {}
        end

        parent = parent[key]

        key = select(j, ...)
        -- We turn any nil argument into false so it can be used as a table
        -- key. This might cause unexpected behaviour for an arbitrary
        -- function.
        if key == nil then
            key = false
        end
    end

    if parent[key] == nil then
        local val = func()
        if val == nil then
            val = false
        end
        parent[key] = val
    end

    return parent[key]
end

function Monster:x_pos()
    return self:property_memo("x_pos")
end

function Monster:y_pos()
    return self:property_memo("y_pos")
end

function Monster:pos()
    return self:property_memo("pos",
        function()
            return { x = self:x_pos(), y = self:y_pos() }
        end)
end

function Monster:map_pos()
    return self:property_memo("map_pos",
        function()
            return position_sum(qw.map_pos, self:pos())
        end)
end

function Monster:distance()
    return self:property_memo("distance",
        function()
            return supdist(self:pos())
        end)
end

function Monster:can_use_doors()
    return self:property_memo("can_use_doors")
end

function Monster:can_traverse(pos)
    if not self.props.traversal_map then
        self.props.traversal_map = {}
    end
    if not self.props.traversal_map[pos.x] then
        self.props.traversal_map[pos.x] = {}
    end
    if self.props.traversal_map[pos.x][pos.y] == nil then
        local val = self.minfo:can_traverse(pos.x, pos.y)
        if not val and self:can_use_doors() then
            local feat = view.feature_at(pos.x, pos.y)
            val = feat == "closed_door" or feat == "closed_clear_door"
        end

        self.props.traversal_map[pos.x][pos.y] = val
    end

    return self.props.traversal_map[pos.x][pos.y]
end

function Monster:name()
    return self:property_memo("name")
end

function Monster:short_name()
    return self:property_memo("short_name",
        function()
            return monster_short_name(self)
        end)
end

function Monster:desc()
    return self:property_memo("desc")
end

function Monster:is_real_hydra()
    return self:property_memo("is_real_hydra",
        function()
            local name = self:name()
            return name:find("hydra")
                and not contains_string_in(name,
                    { "skeleton", "zombie", "simulacrum", "spectral" })
        end)
end
function Monster:move_delay()
    return self:property_memo("move_delay",
        function()
            return monster_move_delay(self)
        end)
end

function Monster:type()
    return self:property_memo("type")
end

function Monster:attitude()
    return self:property_memo("attitude")
end

function Monster:holiness()
    return self:property_memo("holiness")
end

function Monster:res_fire()
    return self:property_memo("res_fire")
end

function Monster:res_cold()
    return self:property_memo("res_cold")
end

function Monster:res_shock()
    return self:property_memo("res_shock")
end

function Monster:res_poison()
    return self:property_memo("res_poison")
end

function Monster:res_draining()
    return self:property_memo("res_draining")
end

function Monster:res_corr()
    return self:property_memo("res_corr")
end

function Monster:is_immune_vampirism()
    return self:property_memo("is_immune_vampirism",
        function()
            local holiness = self:holiness()
            return self:is_summoned()
                or self:is_harmless()
                or holiness ~= "natural" and holiness ~= "plant"
                or self:res_draining() >= 3
        end)
end

function Monster:res_holy()
    return self:property_memo("res_holy",
        function()
            local holiness = self:holiness()
            return (holiness ~= "undead" and holiness ~= "demonic") and 1 or 0
        end)
end

function Monster:is_safe()
    return self:property_memo("is_safe")
end

function Monster:is_friendly()
    return self:property_memo("is_friendly",
        function()
            return self:attitude() == const.attitude.friendly
        end)
end

function player_can_attack_monster(mons, attack_index)
    if mons:name() == "orb of destruction"
            or mons:attacking_causes_penance() then
        return false
    end

    if not attack_index then
        return true
    end

    local attack = get_attack(attack_index)
    if attack.type == const.attack.melee then
        return mons:player_can_melee()
    end

    if attack.type == const.attack.launcher then
        return not unable_to_shoot()
            and mons:player_has_line_of_fire(attack_index)
    elseif attack.type == const.attack.throw then
        return not unable_to_throw()
            and mons:player_has_line_of_fire(attack_index)
    elseif attack.type == const.attack.evoke then
        return can_evoke() and mons:player_has_line_of_fire(attack_index)
    end
end

function Monster:player_can_attack(attack_index)
    return self:property_memo_args("player_can_attack",
        function()
            return player_can_attack_monster(self, attack_index)
        end, attack_index)
end

function Monster:attacking_causes_penance()
    return self:property_memo("attacking_causes_penance",
        function()
            return self:attitude() > const.attitude.hostile and is_good_god()
                or self:attitude() == const.attitude.strict_neutral
                    and you.god() == "Jiyva"
                or self:is_friendly()
                    and you.god() == "Beogh"
                    -- XXX: For simplicity, just assume any non-summoned
                    -- friendly is a follower orc.
                    and not self:is_summoned()
        end)
end

function Monster:is_orc_priest_wizard()
    return self:property_memo("is_orc_priest_wizard",
        function()
            local name = self:name()
            return name == "orc priest" or name == "orc wizard"
        end)
end

-- Monsters here will be target with ranged attacks even if they're not the
-- closest monster.
function Monster:los_danger()
    return self:property_memo("los_danger",
        function()
            local name = self:name()
            return name == "doom hound" and self:is("ready_to_howl")
                or name == "draconian shifter"
                or name == "dream sheep"
                or name == "entropy weaver"
                or name == "glass eye"
                or name == "guardian serpent"
                or name == "hellion"
                or name == "moth of wrath"
                or name == "torpor snail"
        end)
end

function Monster:ignores_player_projectiles()
    return self:property_memo("ignores_player_projectiles",
        function()
            return self:name() == "bush"
                or self:name() == "orb of destruction"
                or self:holiness() == "plant" and you.god() == "Fedhas"
                or self:name():find("^elliptic") and you.god() == "Hepliaklqana"
        end)
end

function Monster:threat(duration_level)
    return self:property_memo_args("threat",
        function()
            return monster_threat(self, duration_level)
        end, duration_level)
end

function Monster:hp()
    return self:property_memo("hp",
        function()
            local hp = self.minfo:max_hp():gsub(".-(%d+).*", "%1")
            return tonumber(hp)
                -- The scaling factor takes the midpoint hitpoint value for the
                -- damage level.
                * min(1, max(0, (10 - 2 * self.minfo:damage_level() + 1) / 10))
        end)
end

function Monster:player_attack_damage(index, duration)
    return self:property_memo_args("player_attack_damage",
        function()
            return player_attack_damage(self, index, duration)
        end, index, duration)
end

function Monster:best_player_attack()
    return self:property_memo("best_player_attack",
        function() return monster_best_player_attack(self) end)
end

function Monster:is_stationary()
    return self:property_memo("is_stationary")
end

-- Adding some clua for this would be better.
function Monster:is_liquid_bound()
    return self:property_memo("is_liquid_bound",
        function()
            local name = self:name()
            return name == "electric eel"
                or name == "kraken"
                or name == "elemental wellspring"
                or name == "lava snake"
        end)
end

-- Adding some clua for this too would be better.
function Monster:can_use_stairs()
    return self:property_memo("can_use_upstairs",
        function()
            local name = self:name()
            return not (self:is_stationary()
                or self:is_liquid_bound()
                or self:is_summoned()
                or name:find("zombie")
                or name:find("skeleton")
                or name:find("spectral")
                or name:find("simulacrum")
                or name:find("tentacle")
                or name:find("vortex")
                or name == "silent spectre"
                or name == "Geryon"
                or name == "Royal Jelly"
                or name == "bat"
                or name == "unseen horror"
                or name == "harpy")
        end)
end

function Monster:damage_level()
    return self:property_memo("damage_level")
end

function Monster:is_caught()
    return self:property_memo("is_caught")
end

function Monster:is_summoned()
    return self:property_memo("is_summoned",
        function()
            return self:is("summoned")
        end)
end

function Monster:reach_range()
    return self:property_memo("reach_range")
end

function Monster:is_constricted()
    return self:property_memo("is_constricted")
end

function Monster:is_constricting_you()
    return self:property_memo("is_constricting_you")
end

function Monster:stabbability()
    return self:property_memo("stabbability")
end

function Monster:is_ranged(ignore_reach)
    return self:property_memo_args("is_ranged",
        function()
            -- The has_known_ranged_attack() moninf method was removed in
            -- DCSS 0.34. Its threat_range ("maximum range with a weapon,
            -- spell, or wand") covers the same cases: launchers, missiles,
            -- offensive spells and wands, and melee reach.
            return self.minfo:range() > 1
                    and not (ignore_reach and self:reach_range() > 1
                        or self:name():find("kraken")
                        or self:name() == "lost soul")
                -- We want to treat these as ranged.
                or self:name() == "obsidian statue"
        end, ignore_reach)
end

function Monster:is_harmless()
    return self:property_memo("is_harmless",
        function()
            return self.minfo:is_firewood() or self:name() == "butterfly"
        end)
end

-- Whether we'd ever want to attack this monster, and hence whether it'll be
-- put in the enemy list.
function Monster:is_enemy()
    return self:property_memo("is_enemy",
        function()
            if self:is_harmless() then
                return false
            end

            if self:name() == "orb of destruction" then
                return false
            end

            local attitude = self:attitude()
            return attitude < const.attitude.neutral
                or attitude == const.attitude.neutral and self:is("frenzied")
        end)
end

-- Whether the player can melee this monster right now.
function Monster:player_can_melee()
    return self:property_memo("player_can_melee",
        function()
            return player_can_melee_mons(self)
        end)
end

function Monster:is_unalert()
    return self:property_memo("is_unalert",
        function()
            return self:is("sleeping")
                or self:is("dormant")
                or self:is("wandering")
        end)
end

function Monster:can_seek(ignore_temporary)
    return self:property_memo_args("can_seek",
        function()
            if self:is_stationary()
                    or self:is_unalert()
                    or self:name() == "wandering mushroom"
                    or self:name():find("vortex") then
                return false
            end

            if ignore_temporary then
                return true
            end

            return not (self:is_caught()
                or self:is_constricted()
                or self:is("fleeing")
                or self:status("paralysed")
                or self:status("confused")
                or self:status("petrified")
                or self:status("constricted by roots"))
        end, ignore_temporary)
end

function Monster:can_melee_at(pos)
    if not self.props.can_melee_at then
        self.props.can_melee_at = {}
    end
    if not self.props.can_melee_at[pos.x] then
        self.props.can_melee_at[pos.x] = {}
    end

    if self.props.can_melee_at[pos.x][pos.y] ~= nil then
        return self.props.can_melee_at[pos.x][pos.y]
    end

    local can_melee = positions_can_melee(self:pos(), pos, self:reach_range())
    self.props.can_melee_at[pos.x][pos.y] = can_melee
    return can_melee
end

function Monster:can_melee_player()
    return self:can_melee_at(const.origin)
end

function Monster:melee_move_search(pos)
    if not self.props.melee_move_search then
        self.props.melee_move_search = {}
    end
    if not self.props.melee_move_search[pos.x] then
        self.props.melee_move_search[pos.x] = {}
    end

    if self.props.melee_move_search[pos.x][pos.y] ~= nil then
        return self.props.melee_move_search[pos.x][pos.y]
    end

    if not self:can_seek(true) then
        self.props.melee_move_search[pos.x][pos.y] = false
        return false
    end

    local square_func = function(pos)
        return self:can_traverse(pos)
    end
    local result = move_search(self:pos(), pos, square_func,
        self:reach_range())
    self.props.melee_move_search[pos.x][pos.y] = result
    return result
end

function Monster:melee_move_distance(pos)
    if position_distance(self:pos(), pos) <= self:reach_range() then
        return 0
    end

    local result = self:melee_move_search(pos)
    if result then
        return result.dist
    else
        return const.inf_dist
    end
end

--[[
Whether this monster has a path it can take to melee the player. This includes
the case where the monster is already in range to melee.

@treturn boolean True if the monster has such a path, false otherwise.
]]--
function Monster:has_path_to_melee_player()
    return self:property_memo("has_path_to_melee_player",
        function()
            if self:can_melee_player() then
                return true
            end

            return self:melee_move_search(const.origin)
        end)
end

--[[
Whether this monster has a path it can take to get adjacent to the player.
This includes the case where the monster is already adjacent.

@treturn boolean True if the monster has such a path, false otherwise.
]]--
function Monster:has_path_to_player()
    return self:property_memo("has_path_to_player",
        function()
            if not self:can_seek() then
                return false
            end

            if position_distance(self:pos(), const.origin) == 1 then
                return true
            end

            local square_func = function(pos)
                return self:can_traverse(pos)
            end
            return move_search(self:pos(), const.origin, square_func, 1)
        end)
end

function Monster:player_can_wait_for_melee()
    return self:property_memo("player_can_wait_for_melee",
        function()
            return not self:player_can_melee()
                and self:has_path_to_melee_player()
                and (self:reach_range() <= player_reach_range()
                        or get_move_closer(self:pos()))
                and self:distance() > self:reach_range()
        end)
end

function Monster:player_has_line_of_fire(attack_id)
    return self:property_memo_args("player_has_line_of_fire",
        function()
            return player_has_line_of_fire(self:pos(), attack_id)
        end, attack_id)
end

function Monster:adjacent_cells_known()
    return self:property_memo("adjacent_cells_known",
        function()
            for pos in adjacent_iter(self:pos()) do
                if view.feature_at(pos.x, pos.y) == "unseen" then
                    return false
                end
            end
            return true
        end)
end

function Monster:should_dig_unreachable()
    return self:property_memo("should_dig_unreachable",
        function()
            return should_dig_unreachable_monster(self)
        end)
end

function Monster:is(flag)
    return self:property_memo_args("is",
        function()
            return self.minfo:is(flag)
        end, flag)
end

function Monster:status(status)
    return self:property_memo_args("status",
        function()
            return self.minfo:status(status)
        end, status)
end

function Monster:player_has_path_to_melee()
    return self:property_memo("player_has_path_to_melee",
        function()
            if self:player_can_melee() then
                return true
            end

            return move_search(const.origin, self:pos(),
                traversal_function(), player_reach_range())
        end)
end

function Monster:get_player_move_towards(assume_flight)
    return self:property_memo_args("get_player_move_towards",
        function()
            local result = move_search(const.origin, self:pos(),
                tab_function(assume_flight), player_reach_range())
            return result and result.move or false
        end, assume_flight)
end

function Monster:weapon_accuracy(item)
    return self:property_memo_args("weapon_accuracy",
        function()
            local str = self.minfo:target_weapon(item)
            str = str:gsub(".-(%d+)%% to hit.*", "%1")
            return tonumber(str) / 100
        end, item)
end

function Monster:throw_accuracy(item)
    return self:property_memo_args("throw_accuracy",
        function()
            local str = self.minfo:target_throw(item)
            str = str:gsub(".-(%d+)%% to hit.*", "%1")
            return tonumber(str) / 100
        end, item)
end

function Monster:evoke_accuracy(item)
    return self:property_memo_args("evoke_accuracy",
        function()
            local str = self.minfo:target_evoke(item)
            if empty_string(str) then
                return 1
            end

            -- Comes in two forms: "XX% to hit" and "chance to affect: XX%".
            str = str:gsub(".-(%d+)%%.*", "%1")
            local perc = tonumber(str)
            if not perc then
                return 0
            end

            return perc / 100
        end, item)
end
-----------------------------------------
-- monster functions and data

-- The enum value of MONS_PANDEMONIUM_LORD, which changes whenever monsters
-- are added or removed. This is the value for DCSS 0.34 (verified by
-- compiling monster-type.h from the 0.34.1 tag).
const.pan_lord_type = 344

const.attitude = {
    "hostile",
    "neutral",
    "strict_neutral",
    "peaceful",
    "friendly"
}

const.moderate_threat = 5
const.high_threat = 10
const.extreme_threat = 20

function moderate_threat_level()
    return const.moderate_threat - max(0, min(3, 10 - you.xl()))
end

function high_threat_level()
    return const.high_threat - max(0, min(5, 2 * (10 - you.xl())))
end

function extreme_threat_level()
    return const.extreme_threat - max(0, min(10, 2 * (10 - you.xl())))
end

-- functions for use in the monster lists below
function in_desc(lev, str)
    return function (mons)
        return you.xl() < lev and mons:desc():find(str)
    end
end

function pan_lord(lev)
    return function (mons)
        return you.xl() < lev and mons:type() == const.pan_lord_type
    end
end

local player_resist_funcs = {
    rF=you.res_fire,
    rC=you.res_cold,
    rPois=you.res_poison,
    rElec=you.res_shock,
    rN=you.res_draining,
    -- returns a boolean
    rCorr=function() return you.res_corr() and 1 or 0 end,
    Will=you.willpower,
}

function check_resist(lev, resist, value)
    return function (enemy)
        return you.xl() < lev and player_resist_funcs[resist]() < value
    end
end

function slow_berserk(lev)
    return function (enemy)
        return you.xl() < lev and count_enemies(1) > 0
    end
end

function hydra_weapon_value(weap)
    if not weap then
        return 0
    end

    local sk = weap.weap_skill
    if sk == "Ranged Weapons"
            or sk == "Maces & Flails"
            or sk == "Short Blades"
            or sk == "Polearms" and weap.hands == 1 then
        return 0
    elseif weap.ego() == "flaming" then
        return 2
    else
        return -2
    end
end

function hydra_melee_value()
    local total_value = 0
    for weapon in equipped_slot_iter("weapon") do
        total_value = total_value + hydra_weapon_value(weapon)
    end
    return total_value
end

function hydra_is_scary(mons)
    if hydra_melee_value() > 0 then
        return false
    end

    if unable_to_swap_weapons() then
        return true
    end

    local best_weapon = best_hydra_swap_weapon()
    return hydra_weapon_value(best_weapon) <= 0
end

-- The format in monster lists below is that a num is equivalent to checking
-- XL < num, otherwise we want a function. ["*"] should be a table of
-- functions to check for every monster.
local scary_monsters = {
    ["ice beast"] = { xl = 7, resists = { rC = 0.75 } },

    ["fire crab"] = { xl = 14, resists = { rF = 0.65} },
    ["wolf spider"] = { xl = 14 },
    ["ice statue"] = { xl = 14, resists = { rC = 1 } },

    ["white ugly thing"] = { xl = 15, resists = { rC = 0.75 } },
    ["freezing wraith"] = { xl = 15, resists = { rC = 0.75 } },
    ["skeletal warrior"] = { xl = 15 },
    ["fire dragon"] = { xl = 15, resists = {rF = 0.5 } },
    ["ice dragon"] = { xl = 15, resists = {rC = 0.5 } },

    ["hydra"] = { xl = 17, check = hydra_is_scary },
    ["entropy weaver"] = { xl = 17, resists = { rCorr = 0.75 } },
    ["shock serpent"] = { xl = 17, resists = { rElec = 0.75 } },
    ["spark wasp"] = { xl = 17, resists = { rElec = 0.75 } },
    ["sun demon"] = { xl = 17, resists = { rF = 0.75 } },
    ["white very ugly thing"] = { xl = 17, resists = { rC = 0.75 } },
    ["Lodul"] = { xl = 17, resists = { rElec = 0.75 } },

    ["ironbound frostheart"] = { xl = 20, resists = { rC = 0.75 } },
    ["ironbound thunderhulk"] = { xl = 20, resists = { rElec = 0.75 } },
    ["hoarfrost cannon"] = { xl = 20, resists = { rC = 0.75 } },

    ["apis"] = { xl = 24 },
    ["azure jelly"] = { xl = 24, resists = { rC = 0.75 } },
    ["boundless tesseract"] = { xl = 24 },
    ["enormous slime creature"] = { xl = 24 },
    ["fire giant"] = { xl = 24, resists = { rF = 0.75 } },
    ["frost giant"] = { xl = 24, resists = { rC = 0.75 } },
    ["hell hog"] = { xl = 24, resists = { rF = 0.75 } },
    ["hellfire mortar"] = { xl = 24, resists = { rF = 0.75 } },
    ["orange crystal statue"] = { xl = 24 },
    ["orb of winter"] = { xl = 24, resists = { rC = 0.75 } },
    ["shadow dragon"] = { xl = 24, resists = { rN = 0.75 } },
    ["spriggan air mage"] = { xl = 24, resists = { rElec = 0.75 } },
    ["star jelly"] = { xl = 24, resists = { rCorr = 0.75 } },
    ["storm dragon"] = { xl = 24, resists = { rElec = 0.75 } },
    ["titan"] = { xl = 24, resists = { rElec = 0.5 } },
    ["Margery"] = { xl = 24, resists = { rF = 0.75 } },
    ["Xtahua"] = { xl = 24, resists = { rF = 0.75 } },

    ["daeva"] = { xl = 30 },
    ["hellion"] = { xl = 30 },
    ["titanic slime creature"] = { xl = 30 },
    ["doom hound"] = { xl = 30,
        check = function(mons) return mons:is("ready_to_howl") end },
    ["electric golem"] = { xl = 30, resists = { rElec = 1 } },
    ["orb of fire"] = { xl = 30, resists = { rF = 1 } },
    ["pandemonium lord"] = { xl = 30 },
    ["player ghost"] = { xl = 30 },

    ["Antaeus"] = { xl = 34 },
    ["Asmodeus"] = { xl = 34 },
    ["Lom Lobon"] = { xl = 34 },
    ["Cerebov"] = { xl = 34 },
}

-- Trog's Hand these.
local hand_monsters = {
    ["*"] = {},

    ["Grinder"] = 10,

    ["orc sorcerer"] = 17,
    ["wizard"] = 17,

    ["ogre mage"] = 100,
    ["Rupert"] = 100,
    ["Xtahua"] = 100,
    ["Aizul"] = 100,
    ["Erolcha"] = 100,
    ["Louise"] = 100,
    ["lich"] = 100,
    ["ancient lich"] = 100,
    ["dread lich"] = 100,
    ["Kirke"] = 100,
    ["golden eye"] = 100,
    ["deep elf sorcerer"] = 100,
    ["deep elf demonologist"] = 100,
    ["sphinx"] = 100,
    ["great orb of eyes"] = 100,
    ["vault sentinel"] = 100,
    ["the Enchantress"] = 100,
    ["satyr"] = 100,
    ["fenstrider witch"] = 100,
    ["vampire knight"] = 100,
    ["siren"] = 100,
    ["merfolk avatar"] = 100,
}

-- Potion of resistance these.
local fire_resistance_monsters = {
    ["*"] = {},

    ["fire crab"] = check_resist(14, "rF", 1),

    ["hellephant"] = check_resist(100, "rF", 2),
    ["orb of fire"] = 100,

    ["Asmodeus"] = check_resist(100, "rF", 2),
    ["Cerebov"] = 100,
    ["Margery"] = check_resist(100, "rF", 2),
    ["Xtahua"] = check_resist(100, "rF", 2),
    ["Vv"] = check_resist(100, "rF", 2),
}

local cold_resistance_monsters = {
    ["*"] = {},

    ["ice beast"] = check_resist(5, "rC", 1),

    ["white ugly thing"] = check_resist(13, "rC", 1),
    ["freezing wraith"] = check_resist(13, "rC", 1),

    ["Ice Fiend"] = 100,
    ["orb of winter"] = 100,
    ["Vv"] = 100,
}

local elec_resistance_monsters = {
    ["*"] = {
        in_desc(20, "black draconian"),
    },
    ["ironbound thunderhulk"] = 20,
    ["storm dragon"] = 20,
    ["electric golem"] = 100,
    ["spark wasp"] = 100,
    ["Antaeus"] = 100,
}

local pois_resistance_monsters = {
    ["*"] = {},
    ["swamp drake"] = 100,
}

local acid_resistance_monsters = {
    ["*"] = {},
    ["acid blob"] = 100,
}

function update_invis_monsters(closest_invis_pos)
    if you.see_invisible() then
        invis_monster = false
        invis_monster_turns = 0
        invis_monster_pos = nil
        nasty_invis_caster = false
        return
    end

    -- A visible nasty monster that can go invisible and whose position we
    -- prioritize tracking over any currently invisible monster.
    if you.xl() < 10 then
        for _, enemy in ipairs(qw.enemy_list) do
            if enemy:name() == "Sigmund" then
                invis_monster = false
                nasty_invis_caster = true
                invis_monster_turns = 0
                invis_monster_pos = enemy:pos()
                return
            end
        end
    end

    if closest_invis_pos then
        invis_monster = true
        if not invis_monster_turns then
            invis_monster_turns = 0
        end
        invis_monster_pos = closest_invis_pos
    end

    if not qw.position_is_safe or options.autopick_on then
        invis_monster = false
        nasty_invis_caster = false
    end

    if invis_monster and invis_monster_turns > 100 then
        say("Invisibility monster not found???")
        invis_monster = false
    end

    if not invis_monster then
        if not options.autopick_on then
            magic(control('a'))
            qw.do_dummy_action = false
            coroutine.yield()
        end

        invis_monster_turns = 0
        invis_monster_pos = nil
        return
    end

    invis_monster_turns = invis_monster_turns + 1
end

-- This returns a value for monster movement energy that's on the aut scale,
-- so that reasoning about the difference between player and monster move
-- delay is easier.
function monster_move_delay(mons)
    local desc = mons.minfo:speed_description()
    local delay = 10
    if desc:find("travel:") then
        -- We only want to pass the first return value of gsub() to
        -- tonumber().
        delay = desc:gsub(".*travel: (%d+)%%.*", "%1")
        -- We're converting a percentage that's based on monsters delay/energy
        -- to aut, since this is easier to compare to player actions.
        delay = 10 * 100 / tonumber(delay)
    elseif desc:find("Speed:") then
        delay = desc:gsub(".*Speed: (%d+)%%.*", "%1")
        delay = 10 * 100 / tonumber(delay)
    end

    -- Assume these move at their roll delay so we won't try to kite.
    if mons:name():find("boulder beetle") then
        delay = delay - 5
    end

    local feat = view.feature_at(mons:x_pos(), mons:y_pos())
    if (feat == "shallow_water" or feat == "deep_water" or feat == "lava")
            and not mons:is("airborne") then
        if desc:find("swim:") then
            delay = desc:gsub(".*swim: (%d+)%%.*", "%1")
            delay = 10 * 100 / tonumber(delay)
        else
            delay = 1.6 * delay
        end
    end

    if mons:is("hasted") or mons:is("berserk") then
        delay = 2 / 3 * delay
    end

    if mons:is("slowed") then
        delay = 1.5 * delay
    end

    return delay
end

function initialize_monster_map()
    qw.monster_map = {}
    for x = -qw.los_radius, qw.los_radius do
        qw.monster_map[x] = {}
    end
end

function update_monsters()
    qw.enemy_list = {}
    qw.slow_aura = false
    qw.all_enemies_safe = true

    local closest_invis_pos
    local sinv = you.see_invisible()

    for pos in radius_iter(const.origin) do
        if you.see_cell_no_trans(pos.x, pos.y) then
            local mon_info = monster.get_monster_at(pos.x, pos.y)
            if mon_info then
                local mons = Monster:new(mon_info)
                qw.monster_map[pos.x][pos.y] = mons
                if mons:is_enemy() then
                    if not mons:is_safe() then
                        qw.all_enemies_safe = false
                    end

                    if mons:name() == "torpor snail" then
                        qw.slow_aura = true
                    end

                    table.insert(qw.enemy_list, mons)
                end
            else
                qw.monster_map[pos.x][pos.y] = nil
            end

            if not sinv
                    and not closest_invis_pos
                    and view.invisible_monster(pos.x, pos.y)
                    and you.see_cell_solid_see(pos.x, pos.y) then
                closest_invis_pos = pos
            end
        else
            qw.monster_map[pos.x][pos.y] = nil
        end
    end

    update_invis_monsters(closest_invis_pos)
end

function get_monster_at(pos)
    if supdist(pos) <= qw.los_radius then
        return qw.monster_map[pos.x][pos.y]
    end
end

function get_closest_enemy()
    if #qw.enemy_list > 0 then
        return qw.enemy_list[1]
    end
end

function monster_in_list(mons, mons_list)
    local entry = mons_list[mons:name()]
    if type(entry) == "number" and you.xl() < entry then
        return true
    elseif type(entry) == "function" and entry(mons) then
        return true
    end

    for _, entry in ipairs(mons_list["*"]) do
        if entry(mons) then
            return true
        end
    end

    return false
end

function assess_enemies_func(duration_level, radius, filter)
    if not radius then
        radius = qw.los_radius
    end

    local result = { count = 0, threat = 0, ranged_threat = 0, move_delay = 0 }
    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:distance() > radius then
            break
        end

        local ranged = enemy:is_ranged(true)
        if (not filter or filter(enemy))
                and (ranged or enemy:has_path_to_melee_player()) then
            local threat = enemy:threat(duration_level)
            result.threat = result.threat + threat
            if ranged then
                result.ranged_threat = result.ranged_threat + threat
            end

            if not result.scary_enemy and threat >= 3 then
                result.scary_enemy = enemy
            end

            result.move_delay = result.move_delay + enemy:move_delay() * threat
            result.count = result.count + 1
        end
    end
    result.move_delay = result.move_delay / result.threat

    return result
end

function assess_enemies(duration_level, radius, filter)
    return turn_memo_args("assess_enemies",
        function()
            return assess_enemies_func(duration_level, radius, filter)
        end, duration_level, radius, filter)
end

function have_moderate_threat(duration_level)
    local enemies = assess_enemies(duration_level)
    return enemies.threat >= moderate_threat_level()
end

function have_high_threat(duration_level)
    local enemies = assess_enemies(duration_level)
    return enemies.threat >= high_threat_level()
end

function have_extreme_threat(duration_level)
    local enemies = assess_enemies(duration_level)
    return enemies.threat >= extreme_threat_level()
end

function get_scary_enemy(duration_level)
    local enemies = assess_enemies(duration_level)
    return enemies.scary_enemy
end

function mons_res_holy_check(mons)
    return mons:res_holy() <= 0
end

function mons_tso_heal_check(mons)
    return mons:res_holy() <= 0 and not mons:is_summoned()
end

function assess_hell_enemies(radius)
    if not in_hell_branch() then
        return { threat = 0, ranged_threat, count = 0 }
    end

    -- We're most concerned with hell monsters that aren't vulnerable to any
    -- holy wrath we might have (either from TSO Cleansing Flame or the weapon
    -- brand).
    local have_holy_wrath = you.god() == "the Shining One"
    for weapon in equipped_slot_iter("weapon") do
        if weapon.ego() == "holy wrath" then
            have_holy_wrath = true
        end
    end

    local filter = function(mons)
        return not have_holy_wrath or mons:res_holy() > 0
    end
    return assess_enemies(radius, const.duration.active, filter)
end

function check_enemies_func(radius, filter)
    local i = 0
    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:distance() <= radius and (not filter or filter(enemy)) then
            return true
        end
    end

    return false
end

function check_enemies(radius, filter)
    return turn_memo_args("check_enemies",
        function()
            return check_enemies_func(radius, filter)
        end, radius, filter)
end

function check_enemies_in_list(radius, mons_list)
    local filter = function(enemy)
        return monster_in_list(enemy, mons_list)
    end
    return check_enemies(radius, filter)
end

function check_immediate_danger()
    local filter = function(enemy)
        local dist = enemy:distance()
        if dist <= 2 then
            return true
        elseif dist == 3 and enemy:reach_range() >= 2 then
            return true
        elseif enemy:is_ranged(true) then
            return true
        end

        return false
    end
    return check_enemies(qw.los_radius, filter)
end

function count_enemies_func(radius, filter)
    local i = 0
    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:distance() <= radius and (not filter or filter(enemy)) then
            i = i + 1
        end
    end
    return i
end

function count_enemies(radius, filter)
    return turn_memo_args("count_enemies",
        function()
            return count_enemies_func(radius, filter)
        end, radius, filter)
end

function count_enemies_by_name(radius, name)
    return count_enemies(radius,
        function(enemy) return enemy:name() == name end)
end

function count_hostile_summons(radius)
    if you.god() ~= "Makhleb" then
        return 0
    end

    return count_enemies(radius,
        function(enemy) return enemy:is_summoned()
            and monster_is_greater_servant(enemy) end)
end

function count_pan_lords(radius)
    return count_enemies(radius,
        function(mons) return mons:type() == const.pan_lord_type end)
end

function should_dig_unreachable_monster(mons)
    if not find_item("wand", "digging") then
        return false
    end

    local grate_mon_list
    if in_branch("Zot") or in_branch("Depths") and at_branch_end() then
        grate_mon_list = {"draconian stormcaller", "draconian scorcher"}
    elseif in_branch("Pan") then
        grate_mon_list = {"smoke demon", "ghost moth"}
    elseif at_branch_end("Geh") then
        grate_mon_list = {"smoke demon"}
    elseif in_branch("Zig") then
        grate_mon_list = {""}
    else
        return false
    end

    return contains_string_in(mons:name(), grate_mon_list)
        and can_dig_to(mons:pos())
end

function monster_short_name(mons)
    local desc = mons:desc()
    if desc:find("hydra") then
        local undead = { "skeleton", "zombie", "simulacrum", "spectral" }
        for _, name in ipairs(undead) do
            if desc:find(name) then
                if name == "spectral" then
                    return "spectral hydra"
                else
                    return "hydra " .. name
                end
            end
        end

        return "hydra"
    end

    if mons:desc():find("'s? ghost") then
        return "player ghost"
    end

    if mons:desc():find("'s? illusion") then
        return "player illusion"
    end

    if mons:type() == const.pan_lord_type then
        return "pandemonium lord"
    end

    return mons:name()
end

function monster_percent_unresisted(resist, level, ego)
    if level < 0 then
        return 1.5
    elseif level == 0 then
        return 1
    end

    if resist == "rF" or resist == "rC" or resist == "rN" or resist == "rCorr" then
        if ego then
            return level > 0 and 0 or 1
        end

        return level == 1 and 0.5 or (level == 2 and 0.2 or 0)
    elseif resist == "rElec" or resist == "rPois" then
        if ego then
            return level > 0 and 0 or 1
        end

        return level == 1 and 0.5 or (level == 2 and 0.25 or 0)
    else
        return 1
    end
end

const.monster_resist_props = {
    ["rF"] = "res_fire",
    ["rC"] = "res_cold",
    ["rElec"] = "res_shock",
    ["rPois"] = "res_poison",
    ["rN"] = "res_draining",
    ["rCorr"] = "res_corr",
    ["rHoly"] = "res_holy",
}

function monster_threat(mons, duration_level)
    if not duration_level then
        duration_level = const.duration.active
    end

    local threat = mons.minfo:threat()
    local entry = scary_monsters[mons:short_name()]
    local player_xl = you.xl()
    if entry and player_xl < entry.xl
            and (not entry.check or entry.check(mons)) then
        threat = threat + entry.xl - player_xl

        local resist_factor = 1
        if entry.resists then
            for resist, factor in pairs(entry.resists) do
                local perc = player_resist_percentage(resist,
                    player_property(resist))
                resist_factor = resist_factor + factor * (perc - 1)
            end
        end
        threat = threat * resist_factor
    end

    if duration_level >= const.duration.active then
        local mons_berserk = mons:is("berserk")
        threat = threat
            -- (3/2)^3 for +50% speed & +50% damage & +50% HP.
            * (mons_berserk and 3.375 or 1)
            * (not mons_berserk and mons:is("strong") and 1.5 or 1)
            * (not mons_berserk and mons:is("hasted") and 1.5 or 1)
            * (mons:is("slowed") and 2 / 3 or 1)
    end

    local attack = get_attack(1)
    -- An optimization: we can avoid weapon delay calculations and use simple
    -- multipliers if we're not incorporating heroism.
    if have_duration("heroism", duration_level) then
        threat = threat * player_attack_delay(1, duration_level)
            / player_attack_delay(1, const.duration.ignore)
    else
        if have_duration("slow", duration_level) then
            threat = threat * 1.5
        end

        if have_duration("finesse", duration_level) then
            threat = threat / 2
        elseif attack.uses_berserk
                and have_duration("berserk", duration_level) then
            threat = 2 * threat / 3
        elseif have_duration("haste", duration_level) then
            threat = 2 * threat / 3
        end
    end

    -- Another optimization: don't bother with this set of damage calculations
    -- if the durations don't apply.
    if get_attack(1).uses_might
            and (have_duration("berserk", duration_level)
                or have_duration("might", duration_level)
                or have_duration("weak", duration_level)) then
        threat = threat * player_attack_damage(mons, 1, const.duration.ignore)
            / player_attack_damage(mons, 1, duration_level)
    end

    return threat
end
----------------------
-- Assessment of fleeing positions

function update_flee_positions()
    qw.flee_positions = {}

    if unable_to_move() then
        return
    end

    local stairs_feats = level_stairs_features(where_branch, where_depth,
        const.dir.up)
    local search_feats = {}
    -- Only retreat to safe stairs with a safe destination.
    for _, feat in ipairs(stairs_feats) do
        local state = get_stairs(where_branch, where_depth, feat)
        local dest_state = get_destination_stairs(where_branch, where_depth,
            feat)
        if (not state or state.safe)
                and (not dest_state or dest_state.safe) then
            table.insert(search_feats, feat)
        end
    end

    local positions, feats = get_feature_map_positions(search_feats)
    if not positions then
        return
    end

    for i, pos in ipairs(positions) do
        local state
        if feats[i] == "escape_hatch_up" then
            state = get_map_escape_hatch(where_branch, where_depth, pos)
        end
        if (not state or state.safe)
                and map_is_reachable_at(pos) then
            if debug_channel("flee") then
                dsay("Adding flee position #"
                    .. tostring(#qw.flee_positions + 1) .. " at "
                    .. cell_string_from_map_position(pos))
            end

            table.insert(qw.flee_positions, pos)
        end
    end
end

function check_following_melee_enemies(radius)
    return check_enemies(radius,
        function(mons)
            return mons:can_melee_player() and mons:can_seek()
        end)
end

function want_to_flee()
    if not qw.can_flee_upstairs then
        return false
    end

    -- If we're stuck in danger a bad form or berserked with a non-melee
    -- weapon, fleeing is our best bet.
    if (qw.danger_in_los or options.autopick_on)
            and (in_bad_form() or you.berserk() and using_ranged_weapon()) then
        return true
    end

    if not qw.danger_in_los then
        if qw.last_flee_turn and you.turns() >= qw.last_flee_turn + 10 then
            qw.last_flee_turn = nil
        end

        if not qw.last_flee_turn then
            return false
        end

        return not buffed() and reason_to_rest(90)
    end

    -- Don't flee from a place were we'll be opportunity attacked, and don't
    -- flee when we have allies close by.
    if check_following_melee_enemies(2) or check_allies(3) then
        return false
    end

    -- When we're at low XL and trying to go up, we want to flee to known
    -- stairs when autoexplore is disabled, instead of engaging in combat. This
    -- rule helps Delvers in particular avoid fights near their starting level
    -- that would get them killed.
    if you.xl() <= 8
            and disable_autoexplore
            and goal_travel.first_dir == const.dir.up
            and not goal_travel.stairs_dir then
        return true
    end

    local enemy = get_scary_enemy(const.duration.available)
    if enemy and enemy:threat(const.duration.available) >= 5
            and enemy:name():find("slime creature")
            and enemy:name() ~= "slime creature" then
        return true
    end

    if have_extreme_threat() then
        return not will_fight_extreme_threat()
    end

    if will_kite() then
        return false
    end

    return not buffed()
        and reason_to_rest(90)
        and qw.starting_spell ~= "Summon Small Mammal"
end

function enemy_can_flee_attack(enemy, flee_dist)
    local dist_to_player = enemy:melee_move_distance(const.origin)
    if not dist_to_player then
        if debug_channel("flee-all") then
            local props = { is_ranged = "ranged", reach_range = "reach",
                move_delay = "move delay" }
            dsay("Ignoring monster that can't reach us: "
                .. monster_string(enemy, props))
        end

        return false
    end

    local closing_dist = dist_to_player
        - (enemy:is_ranged(true) and 4 or 0)
    local dist_gain = flee_dist
        * (player_move_delay() - enemy:move_delay())
        / enemy:move_delay()

    if debug_channel("flee-all") then
        local props = { is_ranged = "ranged", reach_range = "reach",
            move_delay = "move delay" }
        dsay("Evaluating " .. monster_string(enemy, props)
            .. " with a closing distance of "
            .. tostring(closing_dist)
            .. " compared to a distance gain of "
            .. tostring(dist_gain))
    end

    return closing_dist < dist_gain
end

function flee_function(map_pos)
    local pos = position_difference(map_pos, qw.map_pos)
    if view.withheld(pos.x, pos.y) or not is_safe_at(pos) then
        return false
    end

    if supdist(pos) > qw.los_radius then
        return true
    end

    local mons = get_monster_at(pos)
    if mons and not mons:is_friendly() then
        return false
    end

    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:can_melee_at(pos) then
            return false
        end
    end

    return true
end

function can_flee_to_destination(pos)
    local search = distance_map_search(qw.map_pos, pos, flee_function, 0)
    if not search then
        if debug_channel("flee") then
            dsay("Unable to find move to flee position at "
                .. cell_string_from_map_position(pos))
        end

        return false
    end

    if debug_channel("flee") then
        dsay("Evaluating flee position at "
            .. cell_string_from_map_position(pos) .. " with distance "
            .. tostring(search.dist))
    end

    local extreme_threat = have_extreme_threat()
    local flee_attackers = 0
    for _, enemy in ipairs(qw.enemy_list) do
        if enemy_can_flee_attack(enemy, search.dist) then
            flee_attackers = flee_attackers + 1
        end

        if flee_attackers > 2 or not extreme_threat and flee_attackers > 0 then
            if debug_channel("flee") then
                dsay("Not fleeing to " .. cell_string_from_map_position(pos)
                    .. " due to "  .. tostring(flee_attackers)
                    .. " or more attackers gaining distance")
            end

            return false
        end
    end

    if debug_channel("flee") then
        dsay("Able to flee to " .. cell_string_from_map_position(pos))
    end

    return true
end

function get_flee_move()
    if in_bad_form() then
        result = best_move_towards_positions(qw.flee_positions, true)

        if debug_channel("flee") then
            if result then
                dsay("Found bad form flee move to "
                    .. cell_string_from_position(result.move)
                    .. " towards destination "
                    .. cell_string_from_map_position(result.dest))
            else
                dsay("No bad form flee move found towards any destination")
            end
        end

        if not result then
            result = best_move_towards_unexplored(true)
        end

        if debug_channel("flee") then
            if result then
                dsay("Found bad form flee move to "
                    .. cell_string_from_position(result.move)
                    .. " towards destination near unexplored areas at "
                    .. cell_string_from_map_position(result.dest))
            else
                dsay("No bad form flee move found towards unexplored areas")
            end
        end

        return result
    end

    local valid_dests = {}
    for _, pos in ipairs(qw.flee_positions) do
        if can_flee_to_destination(pos) then
            table.insert(valid_dests, pos)
        end
    end

    local result = best_move_towards_positions(valid_dests)

    if debug_channel("flee") then
        if result then
            dsay("Found flee move to "
                .. cell_string_from_position(result.move)
                .. " towards destination "
                .. cell_string_from_map_position(result.dest))
        else
            dsay("No move found towards any flee destination")
        end
    end

    return result
end

function will_flee()
    if not want_to_flee() or unable_to_move() or dangerous_to_move() then
        return false
    end

    return get_flee_move()
end
----------------------
-- Assessment of kiting positions

function kiting_attack_delay()
    local target = get_ranged_target()
    if not target then
        target = get_melee_target()
        if not target then
            return
        end
    end

    return player_attack_delay(target.attack.index)
end

function enemy_needs_attack_distance(enemy, attack_delay)
    if not enemy:has_path_to_melee_player() then
        return false
    end

    return math.ceil(attack_delay / enemy:move_delay())
        >= enemy:melee_move_distance(const.origin)
end

function enemy_allows_kiting(enemy, attack_delay, move_delay)
    if enemy:is_ranged(true) or enemy:los_danger() then
        if debug_channel("kite") then
            local props = { los_danger = "los danger", is_ranged = "ranged" }
            dsay("Unable to kite due to LOS danger or ranged: "
                .. monster_string(enemy, props))
        end

        return false
    end

    if not enemy_needs_attack_distance(enemy, attack_delay) then
        return true
    end

    if enemy:move_delay() <= move_delay then
        if debug_channel("kite") then
            local props = { move_delay = "move delay" }
            dsay("Unable to kite because we are not faster than nearby"
                .. " monster: " .. monster_string(enemy, props))
        end

        return false
    end

    local moves_needed = move_delay / (enemy:move_delay() - move_delay)
    if moves_needed > 6 then
        if debug_channel("kite") then
            local props = { move_delay = "move delay" }
            dsay("Unable to kite since nearby monster requires too many moves"
                .. " to gain distance (" .. tostring(moves_needed) .. "): "
                .. monster_string(enemy, props))
        end

        return false
    end

    return true
end

function want_to_kite()
    if qw.want_to_kite ~= nil then
        return qw.want_to_kite
    end

    qw.want_to_kite = false
    qw.want_to_kite_step = false

    if hp_is_low(50) or you.confused() or in_branch("Abyss") then
        return false
    end

    local enemies = assess_enemies(const.duration.ignore_buffs)
    if enemies.threat < moderate_threat_level()
            and not enemies.scary_enemy then
        return false
    end

    local target = get_ranged_target()
    if not target then
        target = get_melee_target()
        if not target then
            return false
        end

        local enemy = get_monster_at(target.pos)
        if not enemy or enemy:reach_range() >= player_reach_range() then
            return false
        end
    end

    local attack_delay = kiting_attack_delay()
    local move_delay = player_move_delay()

    if debug_channel("kite") then
        dsay("Evaluating kiting with attack delay " .. tostring(attack_delay)
            .. " and move delay " .. tostring(move_delay))
    end

    for _, enemy in ipairs(qw.enemy_list) do
        if debug_channel("kite-all") then
            local props = { los_danger = "los danger", is_ranged = "ranged",
                reach_range = "reach", move_delay = "move delay" }
            dsay("Evaluating " .. monster_string(enemy, props))
        end

        if not enemy_allows_kiting(enemy, attack_delay, move_delay) then
            return false
        end

        -- We take a kiting step if an attack would put us within range of the
        -- monster's melee.
        if not qw.want_to_kite_step
                and enemy_needs_attack_distance(enemy, attack_delay) then
            if debug_channel("kite") then
                local props = { reach_range = "reach",
                    move_delay = "move delay" }
                dsay("Want a kiting step due to nearby "
                    .. monster_string(enemy, props))
            end

            qw.want_to_kite_step = true
        end
    end

    qw.want_to_kite = true
    return true
end

function want_to_kite_step()
    return want_to_kite() and qw.want_to_kite_step
end

function will_kite()
    return want_to_kite()
        and (not want_to_kite_step()
            or qw.tactical_reason == "kiting")
end

function kiting_function(pos)
    return not get_monster_at(pos)
        and not view.withheld(pos.x, pos.y)
        and is_safe_at(pos)
        and (intrinsic_amphibious() or not in_water_at(pos))
end

function assess_kiting_enemy_at(pos, enemy, player_search)
    local result = { avoid_score = 0, see_score = 0, dist_score = 0 }

    if debug_channel("kite-all") then
        local props = { reach_range = "reach", move_delay = "move delay" }
        dsay("Assessing " .. monster_string(enemy, props))
    end

    if not enemy:has_path_to_melee_player() then
        if debug_channel("kite-all") then
            dsay("Ignoring enemy: no path to melee player")
        end

        return result
    end

    local enemy_move_dist = enemy:melee_move_distance(pos)
    if enemy:can_seek(true) and enemy_move_dist == const.inf_dist then
        if debug_channel("kite-all") then
            dsay("Position rejected: " .. enemy:name()
                .. " can't reach this position")
        end

        return
    end

    local move_delay = player_move_delay()
    local attack_delay = kiting_attack_delay()
    local gained_dist = enemy_move_dist
        - player_search.dist * move_delay / enemy:move_delay()
    local min_gain = math.ceil(attack_delay / enemy:move_delay())

    if debug_channel("kite-all") then
        dsay(enemy:name() .. " at " .. pos_string(enemy:pos())
            .. " has move distance " .. tostring(enemy_move_dist)
            .. " and a distance gain of " .. tostring(gained_dist)
            .. " and needs a distance gain of at least "
            .. tostring(min_gain))
    end

    if gained_dist < min_gain then
        if debug_channel("kite-all") then
            dsay("Position rejected: distance gain of " .. enemy:name()
                .. " below minimum required")
        end

        return
    end

    local last_pos
    if enemy:can_melee_player() then
        last_pos = enemy:pos()
    else
        last_pos = enemy:melee_move_search(const.origin).last_pos
    end

    local avoid_score = position_distance(last_pos, player_search.first_pos)
    if enemy:can_melee_player()
            and enemy:reach_range() > 1
            and not enemy:can_melee_at(player_search.first_pos, last_pos) then
        avoid_score = avoid_score + 0.5
    end

    local threat = enemy:threat(const.duration.ignore_buffs)
    result.avoid_score = result.avoid_score + threat * avoid_score
    result.see_score = result.see_score
        + threat * (cell_see_cell(player_search.first_pos, enemy:pos()) and 1 or 0)
    result.dist_score = result.dist_score + threat * gained_dist

    return result
end

function assess_kiting_destination(pos)
    if supdist(pos) < 3 then
        return false
    end

    local search = move_search(const.origin, pos, kiting_function, 0)
    if not search then
        return
    end

    local map_pos = position_sum(qw.map_pos, pos)
    for lpos in square_iter(pos, qw.los_radius) do
        local map_lpos = position_sum(qw.map_pos, lpos)
        if supdist(map_lpos) <= const.gxm
                and traversal_map[map_lpos.x][map_lpos.y] == nil
                and cell_see_cell(pos, lpos) then
            return false
        end
    end

    if debug_channel("kite-all") then
        dsay("Assessing kiting destination " .. cell_string_from_position(pos)
            .. " with move distance " .. tostring(search.dist))
    end

    local result = { pos = pos, map_pos = map_pos, dist = search.dist,
        kite_step = search.first_pos, avoid_score = 0, see_score = 0,
        dist_score = 0 }
    for _, enemy in ipairs(qw.enemy_list) do
        local eresult = assess_kiting_enemy_at(pos, enemy, search)
        if not eresult then
            return
        end

        result.avoid_score = result.avoid_score + eresult.avoid_score
        result.see_score = result.see_score + eresult.see_score
        result.dist_score = result.dist_score + eresult.dist_score
    end

    if debug_channel("kite-all") then
        dsay("Destination has an avoidance score of "
            .. tostring(result.avoid_score)
            .. ", a sight score of "
            .. tostring(result.see_score)
            .. ", and a distance score of "
            .. tostring(result.dist_score))
    end

    return result
end

function result_improves_kiting(result, best_result)
    if not result then
        return false
    end

    if not best_result then
        return true
    end

    return compare_table_keys(result, best_result,
        { "avoid_score", "see_score", "dist_score" })
end

function best_kiting_destination_func()
    if debug_channel("kite") then
        dsay("Assessing kiting destinations with attack delay "
            .. tostring(kiting_attack_delay()) .. " and move delay "
            .. tostring(player_move_delay()))
    end

    local best_result
    for pos in square_iter(const.origin, qw.los_radius) do
        local result = assess_kiting_destination(pos)
        if result_improves_kiting(result, best_result) then
            best_result = result
        end
    end

    if debug_channel("kite") then
        if best_result then
            dsay("Found kiting destination at "
                .. cell_string_from_position(best_result.pos)
                .. " at distance " .. tostring(best_result.dist)
                .. " with an avoidance score of "
                .. tostring(best_result.avoid_score)
                .. " with a sight score of "
                .. tostring(best_result.see_score)
                .. " and a distance score of "
                .. tostring(best_result.dist_score))
        else
            dsay("No kiting destination found")
        end
    end

    return best_result
end

function best_kiting_destination()
    return turn_memo("best_kiting_destination", best_kiting_destination_func)
end

function is_kite_step(pos)
    if not want_to_kite_step() then
        return false
    end

    local result = best_kiting_destination()
    if not result then
        return false
    end

    return positions_equal(result.kite_step, pos)
end
----------------------
-- Assessment of retreat positions

function destination_component(positions, dest_pos)
    local components = {}
    local dest_ind
    local function merge_components(i, j)
        for _, pos in ipairs(components[j]) do
            table.insert(components[i], pos)
        end
        components[j] = nil
        if dest_ind == j then
            dest_ind = i
        end
    end
    for _, pos in ipairs(positions) do
        local target_ind
        for i, component in ipairs(components) do
            for _, cpos in ipairs(component) do
                if is_adjacent(pos, cpos) then
                    if target_ind then
                        merge_components(target_ind, i)
                    else
                        table.insert(component, pos)
                        target_ind = i
                    end

                    break
                end
            end
        end

        if not target_ind then
            table.insert(components, { pos })
            target_ind = #components
        end

        if not dest_ind
                and (positions_equal(pos, dest_pos)
                    or is_adjacent(pos, dest_pos)) then
            dest_ind = target_ind
        end
    end
    return components[dest_ind]
end

function register_destination_enemy(enemy, center, dest_pos, occupied_positions)
    local dest_hash = hash_position(dest_pos)
    if not occupied_positions[dest_hash] and enemy:can_traverse(dest_pos) then
        occupied_positions[dest_hash] = true
        occupied_positions.size = occupied_positions.size + 1
        return
    end

    local positions = {}
    for pos in radius_iter(center, enemy:reach_range()) do
        if enemy:can_traverse(pos)
                and positions_can_melee(center, pos, enemy:reach_range()) then
            table.insert(positions, pos)
        end
    end

    local dest_component = destination_component(positions, dest_pos)
    if not dest_component then
        return
    end

    for _, pos in ipairs(dest_component) do
        local hash = hash_position(pos)
        if not occupied_positions[hash] then
            occupied_positions[hash] = true
            occupied_positions.size = occupied_positions.size + 1
            return
        end
    end
end

function player_last_position_towards(dest_pos)
    local dist_map = get_distance_map(qw.map_pos)
    local best_dist, best_pos
    for pos in adjacent_iter(dest_pos) do
        local map_pos = position_sum(qw.map_pos, pos)
        local dist = dist_map.excluded_map[map_pos.x][map_pos.y]
        if dist and can_move_to(dest_pos, pos)
                and is_safe_at(pos)
                and (not best_dist or dist < best_dist) then
            best_dist = dist
            best_pos = pos
        end
    end
    return best_pos
end

function monster_last_position_towards(mons, pos)
    -- The monster is already as close as they need to be.
    if position_distance(mons:pos(), pos) <= mons:reach_range() then
        return mons:pos()
    end

    local traversal_func = function(tpos)
        return mons:can_traverse(tpos)
    end
    local result = move_search(mons:pos(), pos, traversal_func,
        mons:reach_range())
    if result then
        return result.last_pos
    end
end

function attacking_monster_count_at(pos)
    local occupied_positions = { size = 0 }
    local player_dest_pos
    for _, enemy in ipairs(qw.enemy_list) do
        local dest_pos
        if cell_see_cell(enemy:pos(), pos) then
            dest_pos = monster_last_position_towards(enemy, pos)
        else
            if not player_dest_pos then
                player_dest_pos = player_last_position_towards(pos)
            end
            dest_pos = player_dest_pos
        end

        if dest_pos then
            register_destination_enemy(enemy, pos, dest_pos, occupied_positions)
        end
    end
    return occupied_positions.size
end

function can_retreat_from(from_pos, to_pos)
    if view.withheld(from_pos.x, from_pos.y) or not is_safe_at(from_pos) then
        return false
    end

    -- Once we're in the player's los, we start checking for los-related issues
    -- that prevent movement, such as non-hostile monsters we can't move past
    -- or attack to get out of our way.
    if supdist(to_pos) > qw.los_radius then
        return true
    end

    return not monster_in_way_at(to_pos, from_pos, true)
end

function reverse_retreat_move_to(to_pos, dist_map)
    local map = dist_map.excluded_map
    local to_dist = map[to_pos.x][to_pos.y]
    local to_los_pos = position_difference(to_pos, qw.map_pos)
    local best_pos
    for from_pos in adjacent_iter(to_pos) do
        local from_los_pos = position_difference(from_pos, qw.map_pos)
        -- Moving from from_pos to to_pos must make us closer to the player's
        -- position. We already know that to_pos is on the best path to the
        -- retreat position because we started there and are walking backwards
        -- to the player's position.
        local from_dist = map[from_pos.x][from_pos.y]
        if from_dist
                and from_dist < to_dist
                and can_retreat_from(from_los_pos, to_los_pos) then
            local mons = get_monster_at(from_los_pos)
            -- We prefer a move that doesn't force dealing with a hostile
            -- monster, if one is available.
            if not mons then
                return from_pos, false
            end

            if not best_pos and mons:attitude() < const.attitude.peaceful then
                best_pos = from_pos
            end
        end
    end
    return best_pos, true
end

function assess_retreat_position(map_pos, attacking_limit, max_dist)
    local pos = position_difference(map_pos, qw.map_pos)
    if not is_safe_at(pos) then
        return
    end

    local result = { pos = pos, map_pos = map_pos, num_blocking = 0 }
    result.num_attacking = attacking_monster_count_at(result.pos)

    if attacking_limit and result.num_attacking > attacking_limit then
        return
    end

    -- Further calculations not necessary for our current position.
    if position_is_origin(pos) then
        result.dist = 0
        return result
    end

    local dist_map = get_distance_map(qw.map_pos)
    result.dist = dist_map.excluded_map[map_pos.x][map_pos.y]
    if not result.dist
            or max_dist and result.dist > max_dist then
        return
    end

    -- Walk backwarks from the retreat position until we reach the player's
    -- position.
    local cur_pos = map_pos
    while not positions_equal(cur_pos, qw.map_pos) do
        local pos, has_mons = reverse_retreat_move_to(cur_pos, dist_map)
        if not pos then
            return
        end

        result.num_blocking = result.num_blocking + (has_mons and 1 or 0)
        cur_pos = pos
    end
    return result
end

function result_improves_retreat(retreat, result, best_result)
    if not result then
        return false
    end

    if not best_result then
        return true
    end

    return compare_table_keys(result, best_result, retreat.keys,
        retreat.reversed)
end

function best_retreat_position_func(attacking_limit)
    if not map_is_unexcluded_at(qw.map_pos) then
        return
    end

    if debug_channel("retreat") then
        dsay("Calculating best retreat position with attacking limit "
            .. tostring(attacking_limit))
    end

    local cur_result = assess_retreat_position(qw.map_pos)
    -- Our current location can't significantly improve.
    if cur_result and cur_result.num_attacking <= 1 then
        if debug_channel("retreat") then
            dsay("Can't improve retreat position over current location with "
                .. tostring(cur_result.num_attacking) .. " attacking monster(s)")
        end

        return cur_result
    end

    -- We never retreat further than our closest flee position, if one is
    -- available.
    local radius
    local flee_move = best_move_towards_positions(qw.flee_positions)
    if flee_move then
        radius = max(qw.los_radius, flee_move.dist + 1)
    else
        radius = const.gxm
    end

    local best_result = cur_result
    local retreat = { keys = { "num_blocking", "num_attacking", "dist" },
                      reversed = { num_blocking = true, num_attacking = true,
                          dist = true } }
    local i = 1
    for pos in radius_iter(qw.map_pos, radius) do
        if qw.coroutine_throttle and i % 1000 == 0 then
            if debug_channel("throttle") then
                dsay("Searched block " .. tostring(i / 1000)
                    .. " of potential retreat positions")
            end

            qw.throttle = true
            coroutine.yield()
        end

        if supdist(pos) <= const.gxm
                and map_is_reachable_at(pos)
                and adjacent_floor_map[pos.x][pos.y] < 6
                and not map_has_adjacent_unseen_at(pos) then
            local result = assess_retreat_position(pos, attacking_limit, radius)
            if result_improves_retreat(retreat, result, best_result) then
                best_result = result
            end
        end

        -- We have a good enough result to stop searching. Any subsequent
        -- position can't have a meaningfully lower attacking count and can't
        -- have a lower blocking count or distance at all.
        if best_result
                and best_result.num_attacking <= 1
                and best_result.num_blocking == 0
                and best_result.dist
                    <= position_distance(pos, qw.map_pos) then
            break
        end

        i = i + 1
    end

    if debug_channel("retreat") then
        if best_result then
            dsay("Found best retreat position at "
                .. cell_string_from_map_position(best_result.map_pos)
                .. " with distance " .. tostring(best_result.dist)
                .. " and " .. tostring(best_result.num_blocking)
                .. " blocking monsters"
                .. " and " .. tostring(best_result.num_attacking)
                .. " monsters attacking at destination")
        else
            dsay("No valid retreat position found")
        end
    end

    -- We have no viable retreating position or our current one is rated best.
    if not best_result then
        return
    elseif best_result.dist == 0 then
        if debug_channel("retreat") then
            dsay("Already at best retreat position")
        end

        return best_result
    end

    local enemies = assess_enemies()
    local cutoff
    if cur_result then
        cutoff = (cur_result.num_attacking - best_result.num_attacking)
            * (enemies.threat - enemies.ranged_threat / 2)
            * (10 + enemies.move_delay - player_move_delay()) / 10
    end

    -- Don't try to retreat if we have multiple monsters in the way. Don't try
    -- to retreat too far if our position doesn't improve enough. If our
    -- current position is unsafe such that it is not a valid retreat position,
    -- allow retreating as far as we need to, although in that case, other
    -- plans like cloud tactical step might have acted.
    if best_result.num_blocking > 1
            or cutoff and best_result.dist > cutoff then
        if debug_channel("retreat") then
            if best_result.num_blocking > 1 then
                dsay("Too many monsters blocking retreat")
            else
                dsay("Retreat distance is over cutoff of " .. tostring(cutoff))
            end
        end

        return
    end

    return best_result
end

function best_retreat_position(attacking_limit)
    return turn_memo_args("best_retreat_position",
        function()
            return best_retreat_position_func(attacking_limit)
        end, attacking_limit)
end

function will_fight_extreme_threat()
    if not using_ranged_weapon() then
        return want_to_be_surrounded()
    end

    local result = best_retreat_position(2)
    if not result then
        return false
    end

    return result.dist == 0 or best_move_towards(result.map_pos)
end

function retreat_distance_at(pos)
    if not qw.danger_in_los or not using_ranged_weapon() then
        return const.inf_dist
    end

    local map_pos = position_sum(qw.map_pos, pos)

    if have_extreme_threat(const.duration.available) then
        local result = best_retreat_position(2)
        if not result then
            return const.inf_dist
        elseif positions_equal(map_pos, result.map_pos) then
            return 0
        end

        local move = best_move_towards(result.map_pos, map_pos)
        if move then
            return move.dist + 1
        else
            return const.inf_dist
        end
    end

    local enemies = assess_enemies()
    local adjusted_threat = enemies.threat - enemies.ranged_threat / 2
    if adjusted_threat < moderate_threat_level() then
        if debug_channel("retreat") then
            dsay("No retreat position needed for low adjusted threat of "
                .. tostring(adjusted_threat)
                .. " (total/ranged threat: " .. tostring(enemies.threat)
                .. "/" .. tostring(enemies.ranged_threat) .. ")")
        end

        return const.inf_dist
    end

    local result = best_retreat_position(4)
    if not result then
        return const.inf_dist
    elseif positions_equal(map_pos, result.map_pos) then
        return 0
    end

    local move = best_move_towards(result.map_pos, map_pos)
    if move then
        return move.dist + 1
    end

    return const.inf_dist
end
----------------------
-- Tactical steps

function assess_square_enemies(a)
    local move_delay = player_move_delay()
    local best_dist = const.inf_dist
    a.enemy_dist = 0
    a.followers = false
    a.adjacent = 0
    a.ranged = 0
    a.unalert = 0
    a.longranged = 0
    for _, enemy in ipairs(qw.enemy_list) do
        local dist = enemy:melee_move_distance(a.pos)
        local see_cell = cell_see_cell(a.pos, enemy:pos())
        local ranged = enemy:is_ranged()
        local liquid_bound = enemy:is_liquid_bound()

        if dist < best_dist then
            best_dist = dist
        end

        if dist == 1 then
            a.adjacent = a.adjacent + 1

            if not liquid_bound and not ranged then
                a.followers = true
            end
        end

        if dist > 1
                and see_cell
                and enemy:has_path_to_player()
                and (ranged
                    or dist == 2
                        and enemy:move_delay() < move_delay) then
            a.ranged = a.ranged + 1
        end

        if dist > 1 and see_cell and enemy:is_unalert() then
            a.unalert = a.unalert + 1
        end

        if dist >= 4
                and see_cell
                and ranged
                and enemy:has_path_to_player() then
            a.longranged = a.longranged + 1
        end
    end

    a.enemy_dist = best_dist
end

function assess_square(pos)
    a = { pos = pos }

    -- Distance to current square
    a.supdist = supdist(pos)

    -- Is current square near an ally?
    if a.supdist == 0 then
        a.near_ally = check_allies(3)
    end

    -- Can we move there?
    a.can_move = a.supdist == 0 or can_move_to(pos, const.origin)
    if not a.can_move then
        return a
    end

    local in_water = in_water_at(pos)
    a.sticky_fire_danger = 0
    if not in_water and you.status("on fire") and you.res_fire() < 2 then
        a.sticky_fire_danger = 2 - a.supdist
    end

    -- Avoid corners if possible.
    a.cornerish = is_cornerish_at(pos)

    -- Is the wall next to us dangerous?
    a.bad_walls = count_adjacent_slimy_walls_at(pos)

    -- Will we fumble if we try to attack from this square?
    a.fumble = not using_ranged_weapon() and in_water and intrinsic_fumble()

    -- Will we be slow if we move into this square?
    a.slow = in_water and not intrinsic_amphibious()

    -- Is the square safe to step in? (checks traps & clouds)
    a.safe = is_safe_at(pos)

    -- Would we want to move out of a cloud? We don't worry about weak clouds
    -- if monsters are around.
    a.cloud_dangerous = cloud_is_dangerous_at(pos)

    a.retreat_dist = retreat_distance_at(pos)

    -- Count various classes of monsters from the enemy list.
    assess_square_enemies(a, pos)

    return a
end

-- returns a string explaining why moving a1->a2 is preferable to not moving
-- possibilities are:
--   sticky fire - moving to put out sticky fire
--   cloud       - stepping out of harmful cloud
--   wall        - stepping away from a slimy wall
--   water       - stepping out of shallow water when it would cause fumbling
--   kiting      - kiting slower monsters with a reaching or ranged weapon
--   retreating  - retreating to a better defensive position
--   hiding      - moving out of sight of alert ranged enemies at distance >= 4
--   stealth     - moving out of sight of sleeping or wandering monsters
--   outnumbered - stepping away from adjacent and/or ranged monsters
function step_reason(a1, a2)
    local bad_form = in_bad_form()
    if not (a2.can_move and a2.safe and a2.supdist > 0) then
        return
    elseif a2.sticky_fire_danger < a1.sticky_fire_danger then
        return "sticky fire"
    elseif (a2.fumble or a2.slow or a2.bad_walls > 0) and not a1.cloud_dangerous then
        return
    -- We've already required that a2 is safe.
    elseif a1.cloud_dangerous then
        return "cloud"
    elseif a1.fumble then
        -- We require that we have some close threats we want to melee that
        -- try to stay adjacent to us before we'll try to move out of water.
        -- We also require that we are no worse in at least one of ranged
        -- threats or enemy distance at the new position.
        if (not get_ranged_target() and a1.followers)
                and (a2.ranged <= a1.ranged
                    or a2.enemy_dist <= a1.enemy_dist) then
            return "water"
        else
            return
        end
    elseif a1.bad_walls > 0 then
        -- We move away from bad walls if we're using an attack affected by
        -- the walls. We also use the same additional consideration or ranged
        -- threat and distance as used for water.
        local target = get_ranged_target()
        if (not (target and target.attack.type == const.attack.evoke)
                and a1.followers)
                and (a2.ranged <= a1.ranged
                    or a2.enemy_dist <= a1.enemy_dist) then
            return "wall"
        else
            return
        end
    elseif is_kite_step(a2.pos) then
        return "kiting"
    -- If we're either not kiting or we wanted to kite step but couldn't, it's
    -- ok to retreat. We don't want to retreat if we should be doing a kiting
    -- attack.
    elseif (not want_to_kite() or want_to_kite_step())
            and a2.retreat_dist < a1.retreat_dist then
        return "retreating"
    -- If we have retreated to our retreat position or if we want to kite, we
    -- shouldn't try the step types below. For kiting, it's ok to try the steps
    -- below if we wanted to kite step but couldn't.
    elseif a1.retreat_dist == 0
            or want_to_kite() and not want_to_kite_step() then
        return
    elseif not using_ranged_weapon()
            and not want_to_move_to_abyss_objective()
            and not a1.near_ally
            and a2.ranged == 0
            and a2.adjacent == 0
            and a1.longranged > 0 then
        return "hiding"
    elseif not using_ranged_weapon()
            and not want_to_move_to_abyss_objective()
            and not a1.near_ally
            and a2.ranged == 0
            and a2.adjacent == 0
            and a2.unalert < a1.unalert then
        return "stealth"
    elseif not using_cleave()
            and not using_ranged_weapon()
            and a1.adjacent > 1
            and a2.adjacent + a2.ranged <= a1.adjacent + a1.ranged - 2
            -- We also need to be sure that any monsters we're stepping away
            -- from can eventually reach us, otherwise we'll be stuck in a loop
            -- constantly stepping away and then towards them.
            and qw.incoming_monsters_turn == you.turns() then
        return "outnumbered"
    end
end

-- Determines whether moving a0->a2 is an improvement over a0->a1 assumes that
-- these two moves have already been determined to be better than not moving,
-- with given reasons
function step_improvement(best_reason, reason, a1, a2)
    if reason == "sticky fire"
            and (best_reason ~= "sticky fire"
                or a2.sticky_fire_danger < a1.sticky_fire_danger) then
        return true
    elseif best_reason == "sticky fire"
            and (reason ~= "sticky fire"
                or a2.sticky_fire_danger > a1.sticky_fire_danger) then
        return false
    elseif reason == "cloud" and best_reason ~= "cloud" then
        return true
    elseif best_reason == "cloud" and reason ~= "cloud" then
        return false
    elseif reason == "wall"
            and (best_reason ~= "wall"
                or a2.bad_walls < a1.bad_walls) then
        return true
    elseif best_reason == "wall"
            and (reason ~= "wall"
                or a2.bad_walls > a1.bad_walls) then
        return false
    elseif reason == "water" and best_reason ~= "water" then
        return true
    elseif best_reason == "water" and reason ~= "water" then
        return false
    elseif reason == "kiting" and best_reason ~= "kiting" then
        return true
    elseif best_reason == "kiting" and reason ~= "kiting" then
        return false
    elseif reason == "retreating"
            and (best_reason ~= "retreating"
                or a2.retreat_dist < a1.retreat_dist
                or a2.retreat_dist == a1.retreat_dist
                    and a2.enemy_dist > a1.enemy_dist) then
        return true
    elseif best_reason == "retreating"
            and (reason ~= "retreating"
                or a2.retreat_dist > a1.retreat_dist
                or a2.retreat_dist == a1.retreat_dist
                    and a2.enemy_dist < a1.enemy_dist) then
        return false
    elseif a2.adjacent + a2.ranged < a1.adjacent + a1.ranged then
        return true
    elseif a2.adjacent + a2.ranged > a1.adjacent + a1.ranged then
        return false
    elseif want_to_be_surrounded() and a2.ranged < a1.ranged then
        return true
    elseif want_to_be_surrounded() and a2.ranged > a1.ranged then
        return false
    elseif a2.adjacent + a2.ranged == 0 and a2.unalert < a1.unalert then
        return true
    elseif a2.adjacent + a2.ranged == 0 and a2.unalert > a1.unalert then
        return false
    elseif a2.enemy_dist < a1.enemy_dist then
        return true
    elseif a2.enemy_dist > a1.enemy_dist then
        return false
    elseif a1.cornerish and not a2.cornerish then
        return true
    else
        return false
    end
end

function choose_tactical_step()
    qw.tactical_step = nil
    qw.tactical_reason = nil

    if unable_to_move()
            or dangerous_to_move()
            -- For cloud and sticky fire steps, we'd like to be able to try
            -- these even while confused, so long as we're not also dealing
            -- with monsters.
            or you.confused() and qw.danger_in_los
            or you.berserk() and qw.danger_in_los
            or you.constricted() then
        if debug_channel("move") then
            dsay("No tactical step chosen: not safe to take step")
        end

        return
    end

    local a0 = assess_square(const.origin)
    local danger = check_enemies(3)
    if not a0.cloud_dangerous
            and a0.sticky_fire_danger == 0
            and not (a0.fumble and danger)
            and not (a0.bad_walls > 0 and danger)
            and not want_to_kite()
            and a0.retreat_dist == 0
            and (a0.near_ally or a0.enemy_dist == const.inf_dist) then
        if debug_channel("move") then
            dsay("No tactical step chosen: current position is good enough")
        end

        return
    end

    local best_pos, best_reason, besta
    for pos in adjacent_iter(const.origin) do
        local a = assess_square(pos)
        local reason = step_reason(a0, a)
        if reason then
            if besta == nil
                    or step_improvement(best_reason, reason, besta, a) then
                best_pos = pos
                besta = a
                best_reason = reason
            end
        end
    end
    if besta then
        qw.tactical_step = best_pos
        qw.tactical_reason = best_reason

        if debug_channel("move") then
            dsay("Chose tactical step to "
                .. cell_string_from_position(qw.tactical_step)
                .. " for reason: " .. qw.tactical_reason)
        end

        return
    end

    if debug_channel("move") then
        dsay("No tactical step chosen: no valid step found")
    end
end
----------------------
-- General movement calculations

function can_move_to(to_pos, from_pos, allow_hostiles)
    return is_traversable_at(to_pos)
        and not view.withheld(to_pos.x, to_pos.y)
        and (supdist(to_pos) > qw.los_radius
            or not monster_in_way_at(to_pos, from_pos, allow_hostiles))
end

function traversal_function(assume_flight)
    return function(pos)
        -- XXX: This needs to run before update_map() and hence before
        -- traversal_map is updated, so we have to do an uncached check.
        -- Ideally we'd use the traversal map, but this requires separating
        -- the traversal map update to its own path and somehow retaining
        -- information about the per-cell changes so update_map() can
        -- propagate updates to adjacent cells.
        return feature_is_traversable(view.feature_at(pos.x, pos.y),
            assume_flight)
    end
end

function tab_function(assume_flight)
    return function(pos)
        local mons = get_monster_at(pos)
        if mons and not mons:is_harmless() then
            return false
        end

        return is_safe_at(pos, assume_flight)
            and not view.withheld(pos.x, pos.y)
    end
end

function friendly_can_swap_to(mons, pos)
    return mons:can_seek()
        and mons:can_traverse(pos)
        and view.feature_at(pos.x, pos.y) ~= "trap_zot"
end

function monster_in_way_at(to_pos, from_pos, allow_hostiles)
    local mons = get_monster_at(to_pos)
    if not mons then
        return false
    end

    -- Strict neutral and up will swap with us, but we have to check that
    -- they can. We assume we never want to attack these.
    return mons:attitude() > const.attitude.neutral
            and not friendly_can_swap_to(mons, from_pos)
        or not allow_hostiles
        or not mons:player_can_attack()
end

function get_move_closer(pos)
    local best_move, best_dist
    for apos in adjacent_iter(const.origin) do
        local dist = position_distance(pos, apos)
        if is_safe_at(pos) and (not best_dist or dist < best_dist) then
            best_move = apos
            best_dist = dist
        end
    end

    return best_move, best_dist
end

function search_from(search, pos, current, is_deviation)
    if positions_equal(pos, current) then
        return false
    end

    if debug_channel("move-all") then
        dsay("Checking " .. (is_deviation and "deviation " or "")
            .. "move from " .. cell_string_from_position(current)
            .. " to " .. cell_string_from_position(pos))
    end

    if is_deviation and search.num_deviations >= 2 then
        if debug_channel("move-all") then
            dsay("Too many deviation movements")
        end

        return false
    end

    if position_distance(search.center, pos) > 2 * qw.los_radius then
        if debug_channel("move-all") then
            dsay("Search traveled too far")
        end

        return false
    end

    if not search.attempted[pos.x] then
        search.attempted[pos.x] = {}
    end

    if search.attempted[pos.x][pos.y]
            and search.attempted[pos.x][pos.y] <= search.num_deviations then
        if debug_channel("move-all") then
            dsay("Not attempting previously failed search")
        end

        return false
    end

    if positions_equal(current, search.center) then
        search.first_pos = nil
        search.last_pos = nil
        search.dist = 0
        search.num_deviations = 0
    end

    search.attempted[pos.x][pos.y] = search.num_deviations
        + (is_deviation and 1 or 0)

    if search.square_func(pos) then
        if is_deviation then
            search.num_deviations = search.num_deviations + 1
        end
        search.dist = search.dist + 1

        local set_first_pos = not search.first_pos
        if set_first_pos then
            search.first_pos = pos
        end
        search.last_pos = pos

        if do_move_search(search, pos) then
            return true
        else
            if is_deviation then
                search.num_deviations = search.num_deviations - 1
            end
            search.dist = search.dist - 1

            if set_first_pos then
                search.first_pos = nil
            end

            return false
        end
    end

    if debug_channel("move-all") then
        dsay("Square function failed")
    end

    return false
end

function do_move_search(search, current)
    local diff = position_difference(search.target, current)
    if supdist(diff) <= search.min_dist then
        search.move = position_difference(search.first_pos, search.center)
        return true
    end

    local pos
    local sign_diff_x = sign(diff.x)
    local sign_diff_y = sign(diff.y)
    pos = { x = current.x + sign_diff_x, y = current.y + sign_diff_y }
    if search_from(search, pos, current) then
        return true
    end

    pos = { x = current.x + sign_diff_x, y = current.y }
    if search_from(search, pos, current) then
        return true
    end

    pos = { x = current.x, y = current.y + sign_diff_y}
    if search_from(search, pos, current) then
        return true
    end

    local abs_diff_x = abs(diff.x)
    local abs_diff_y = abs(diff.y)
    if abs_diff_x >= abs_diff_y then
        if abs_diff_y > 0 then
            pos = { x = current.x + sign_diff_x, y = current.y - sign_diff_y }
            if search_from(search, pos, current, true) then
                return true
            end

            pos = { x = current.x - sign_diff_x, y = current.y + sign_diff_y }
            if search_from(search, pos, current, true) then
                return true
            end
        else
            pos = { x = current.x + sign_diff_x, y = current.y + 1 }
            if search_from(search, pos, current, true) then
                return true
            end

            pos = { x = current.x + sign_diff_x, y = current.y - 1 }
            if search_from(search, pos, current, true) then
                return true
            end

            pos = { x = current.x, y = current.y + 1 }
            if search_from(search, pos, current, true) then
                return true
            end

            pos = { x = current.x, y = current.y - 1 }
            if search_from(search, pos, current, true) then
                return true
            end
        end
    elseif abs_diff_x < abs_diff_y then
        if abs_diff_x > 0 then
            pos = { x = current.x - sign_diff_x, y = current.y + sign_diff_y }
            if search_from(search, pos, current, true) then
                return true
            end

            pos = { x = current.x + sign_diff_x, y = current.y - sign_diff_y }
            if search_from(search, pos, current, true) then
                return true
            end
        else
            pos = { x = current.x + 1, y = current.y + sign_diff_y }
            if search_from(search, pos, current, true) then
                return true
            end

            pos = { x = current.x - 1, y = current.y + sign_diff_y }
            if search_from(search, pos, current, true) then
                return true
            end

            pos = { x = current.x + 1, y = current.y }
            if search_from(search, pos, current, true) then
                return true
            end

            pos = { x = current.x - 1, y = current.y }
            if search_from(search, pos, current, true) then
                return true
            end
        end
    end

    return false
end

function move_search(center, target, square_func, min_dist)
    if not min_dist then
        min_dist = 0
    end

    if position_distance(center, target) <= min_dist then
        return
    end

    if debug_channel("move-all") then
        dsay("Move search from " .. cell_string_from_position(center)
            .. " to " .. cell_string_from_position(target))
    end

    search = { center = center, target = target, square_func = square_func,
        min_dist = min_dist, dist = 0, num_deviations = 0 }
    search.attempted = { [center.x] = { [center.y] = 0 } }

    if do_move_search(search, center) then
        return search
    end
end

local move_keys = { "trap", "cloud", "blocked", "unexcluded",
    "melee_count", "slow", "enemy_dist" }
local reversed_move_keys = { trap = true, cloud = true, blocked = true,
    melee_count = true, slow = true }

function assess_move(to_pos, from_pos, dist_map, best_result, use_unsafe)
    local to_los_pos = position_difference(to_pos, qw.map_pos)
    local result = { move = to_los_pos, dest = dist_map.pos,
        safe = not use_unsafe, trap = 0, cloud = 0, blocked = 0,
        unexcluded = 0, melee_count = 0, slow = 0,
        enemy_dist = const.inf_dist }

    if debug_channel("move-all") and map_is_traversable_at(to_pos) then
        dsay("Checking " .. (use_unsafe and "unsafe" or "safe")
            .. " move to " .. cell_string_from_map_position(to_pos))
    end

    local map = use_unsafe and dist_map.map or dist_map.excluded_map
    result.dist = map[to_pos.x][to_pos.y]
    if not result.dist then
        if debug_channel("move-all") and map_is_traversable_at(to_pos) then
            dsay("No path to destination")
        end

        return
    end

    local current_dist = map[from_pos.x][from_pos.y]
    if current_dist and result.dist >= current_dist then
        if debug_channel("move-all") then
            dsay("Distance of " .. tostring(result.dist)
                .. " does not improve the starting position distance of "
                .. tostring(current_dist))
        end

        return
    end

    if best_result and result.dist > best_result.dist then
        if debug_channel("move-all") then
            dsay("Distance of " .. tostring(result.dist)
                .. " is worse than the current best distance of "
                .. tostring(best_result.dist))
        end

        return
    end

    local from_los_pos = position_difference(from_pos, qw.map_pos)
    if not can_move_to(to_los_pos, from_los_pos, use_unsafe) then
        if debug_channel("move-all") then
            dsay("Can't move to position")
        end

        return
    end

    if use_unsafe then
        local feat = view.feature_at(to_los_pos.x, to_los_pos.y)
        local trap
        if feat:find("^trap_") then
            trap = feat:gsub("trap_", "")
        end
        if trap == "zot" then
            result.trap = 2
        elseif not c_trap_is_safe(trap) then
            result.trap = 1
        end

        local cloud = view.cloud_at(to_los_pos.x, to_los_pos.y)
        if cloud_is_dangerous(cloud) then
            result.cloud = 2
        elseif not cloud_is_safe(cloud) then
            result.cloud = 1
        end

        local mons = get_monster_at(to_los_pos)
        if mons and not mons:is_friendly() then
            result.blocked = mons:is_harmless() and 1 or 2
        end

        result.unexcluded = map_is_unexcluded_at(to_pos) and 1 or 0
    elseif not is_safe_at(to_los_pos) then
        if debug_channel("move-all") then
            dsay("Position is not safe")
        end

        return
    end

    if in_water_at(to_los_pos) and not intrinsic_amphibious() then
        result.slow = 1
    end

    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:can_melee_at(to_los_pos) then
            result.melee_count = result.melee_count + 1
        end

        local dist = enemy:melee_move_distance(to_los_pos)
        if dist < result.enemy_dist then
            result.enemy_dist = dist
        end
    end

    if not best_result
            or compare_table_keys(result, best_result, move_keys,
                reversed_move_keys) then
        return result
    end
end

--[[
Get the best move towards the given map position
@table                 dest_pos      The destination map position.
@table[opt=qw.map_pos] from_pos      The starting map position. Defaults to
                                     qw's current position.
@boolean               allow_unsafe  If true, allow movements to squares that
                                     are unsafe due to clouds, traps, etc. or
                                     that contain hostile monsters.
@return nil if no move was found. Otherwise a table with the keys `move` (los
        coordinates of the best move), `dest_pos` (a copy of `dest_pos`),
        `dist` (the distance to `dest_pos` from `move`, and `safe` (true if the
        move is safe).
--]]
function best_move_towards(dest_pos, from_pos, allow_unsafe)
    if not from_pos then
        from_pos = qw.map_pos
    end

    if not map_is_traversable_at(from_pos) then
        return
    end

    local dist_map = get_distance_map(dest_pos)
    local current_dist
    if allow_unsafe then
        current_dist = dist_map.map[from_pos.x][from_pos.y]
    end
    local current_safe_dist = dist_map.excluded_map[from_pos.x][from_pos.y]

    if debug_channel("move-all") then
        local msg = "Determining move from "
            .. cell_string_from_map_position(from_pos)
            .. " to " ..  cell_string_from_map_position(dest_pos)

        if allow_unsafe then
            msg = msg .. " with safe/unsafe distances "
                .. tostring(current_safe_dist) .. "/" .. tostring(current_dist)
        else
            msg = msg .. " safe distance " .. tostring(current_safe_dist)
        end
        dsay(msg)
    end

    if current_safe_dist == 0
            or current_dist == 0
            or not current_safe_dist and not current_dist then
        return
    end

    local best_result
    for pos in adjacent_iter(from_pos) do
        local result = assess_move(pos, from_pos, dist_map, best_result)
        if result then
            best_result = result
        elseif allow_unsafe and (not best_result or not best_result.safe) then
            result = assess_move(pos, from_pos, dist_map, best_result, true)
            if result then
                best_result = result
            end
        end
    end

    return best_result
end

function best_move_towards_positions(map_positions, allow_unsafe)
    local best_result
    for _, pos in ipairs(map_positions) do
        if positions_equal(qw.map_pos, pos) then
            return
        end

        local result = best_move_towards(pos, qw.map_pos, allow_unsafe)
        if result and (not best_result
                or result.safe and not best_result.safe
                or result.dist < best_result.dist) then
            best_result = result
        end
    end
    return best_result
end

function update_reachable_position()
    for _, dist_map in pairs(distance_maps) do
        if dist_map.excluded_map[qw.map_pos.x][qw.map_pos.y] then
            qw.reachable_position = dist_map.pos
            return
        end
    end

    qw.reachable_position = qw.map_pos
end

--[[
Check any feature types flagged in check_reachable_features during the map
update. These have been seen but not are not currently reachable LOS-wise, so
check whether our reachable position distance map indicates they are in fact
reachable, and if so, update their los state.
]]--
function update_reachable_features()
    local check_feats = {}
    for feat, _ in pairs(check_reachable_features) do
        table.insert(check_feats, feat)
    end
    if #check_feats == 0 then
        return
    end

    local positions, feats = get_feature_map_positions(check_feats)
    if #positions == 0 then
        return
    end

    for i, pos in ipairs(positions) do
        if map_is_reachable_at(pos, true) then
            update_feature(where_branch, where_depth, feats[i],
                hash_position(pos), { feat = const.explore.reachable })
        end
    end

    check_reachable_features = {}
end

function map_is_reachable_at(pos, ignore_exclusions)
    local dist_map = get_distance_map(qw.reachable_position)
    local map = ignore_exclusions and dist_map.map or dist_map.excluded_map
    return map[pos.x][pos.y]
end

function best_move_towards_features(feats, allow_unsafe)
    if debug_channel("move") then
        dsay("Determining best move towards feature(s): "
            .. table.concat(feats, ", "))
    end

    local positions = get_feature_map_positions(feats)
    if positions then
        return best_move_towards_positions(positions, allow_unsafe)
    end
end

function best_move_towards_items(item_names, allow_unsafe)
    if debug_channel("move") then
        dsay("Determining best move towards item(s): "
            .. table.concat(item_names, ", "))
    end

    local positions = get_item_map_positions(item_names)
    if positions then
        return best_move_towards_positions(positions, allow_unsafe)
    end
end

function map_has_adjacent_unseen_at(pos)
    for apos in adjacent_iter(pos) do
        if traversal_map[apos.x][apos.y] == nil then
            return true
        end
    end

    return false
end

function map_has_adjacent_runed_doors_at(pos)
    for apos in adjacent_iter(pos) do
        local los_pos = position_difference(apos, qw.map_pos)
        if view.feature_at(los_pos.x, los_pos.y) == "runed_clear_door" then
            return true
        end
    end

    return false
end

function best_move_towards_unexplored_near(map_pos, allow_unsafe)
    if debug_channel("move") then
        dsay("Determining best move towards unexplored squares near "
            .. cell_string_from_map_position(map_pos))
    end

    local i = 1
    for pos in radius_iter(map_pos, const.gxm) do
        if qw.coroutine_throttle and i % 1000 == 0 then
            if debug_channel("throttle") then
                dsay("Searched for unexplored in block " .. tostring(i / 1000)
                    .. " of map positions near "
                    .. cell_string_from_map_position(map_pos))
            end

            qw.throttle = true
            coroutine.yield()
        end

        if supdist(pos) <= const.gxm
                and map_is_reachable_at(pos, allow_unsafe)
                and (open_runed_doors and map_has_adjacent_runed_doors_at(pos)
                    or map_has_adjacent_unseen_at(pos)) then
            return best_move_towards(pos, qw.map_pos, allow_unsafe)
        end

        i = i + 1
    end
end

function best_move_towards_unexplored(allow_unsafe)
    return best_move_towards_unexplored_near(qw.map_pos, allow_unsafe)
end

function best_move_towards_unexplored_near_positions(map_positions,
        allow_unsafe)
    local best_result
    for _, pos in ipairs(map_positions) do
        local result = best_move_towards_unexplored_near(pos, allow_unsafe)
        if result and (not best_result or result.dist < best_result.dist) then
            best_result = result
        end
    end
    return best_result
end

function best_move_towards_safety()
    if debug_channel("move") then
        dsay("Determining best move towards safety")
    end

    local i = 1
    for pos in radius_iter(qw.map_pos, const.gxm) do
        if qw.coroutine_throttle and i % 1000 == 0 then
            if debug_channel("throttle") then
                dsay("Searched for safety in block " .. tostring(i / 1000)
                    .. " of map positions")
            end

            qw.throttle = true
            coroutine.yield()
        end

        local los_pos = position_difference(pos, qw.map_pos)
        if supdist(pos) <= const.gxm
                and is_safe_at(los_pos)
                and map_is_reachable_at(pos, true) then
            return best_move_towards(pos, qw.map_pos, true)
        end

        i = i + 1
    end
end

function update_move_destination()
    if not qw.move_destination then
        qw.move_reason = nil
        return
    end

    local clear = false
    if qw.move_reason == "goal" and qw.want_goal_update then
        clear = true
    elseif qw.move_reason == "monster" and have_target() then
        clear = true
    elseif positions_equal(qw.map_pos, qw.move_destination) then
        if qw.move_reason == "unexplored"
                and autoexplored_level(where_branch, where_depth)
                and qw.position_is_safe then
            reset_autoexplore(where)
        end

        clear = true
    end

    if clear then
        if debug_channel("move") then
            dsay("Clearing move destination "
                .. cell_string_from_map_position(qw.move_destination))
        end

        local dist_map = distance_maps[hash_position(qw.move_destination)]
        if dist_map and not dist_map.permanent then
            distance_map_remove(dist_map)
        end

        qw.move_destination = nil
        qw.move_reason = nil
    end
end

function move_to(pos, cloud_waiting)
    if cloud_waiting == nil then
        cloud_waiting = true
    end

    if cloud_waiting
            and not qw.position_is_cloudy
            and unexcluded_at(pos)
            and cloud_is_dangerous_at(pos) then
        wait_one_turn()
        return true
    end

    local mons = get_monster_at(pos)
    if mons and monster_in_way_at(pos, const.origin, true) then
        if mons:player_can_attack() then
            return shoot_launcher(pos)
        else
            return false
        end
    end

    magic(delta_to_vi(pos) .. "YY")
    return true
end

function move_towards_destination(pos, dest, reason)
    if move_to(pos) then
        qw.move_destination = dest
        qw.move_reason = reason
        return true
    end

    return false
end

function distance_map_search_from(search, pos, current)
    if positions_equal(pos, current) then
        return false
    end

    if debug_channel("move-all") then
        dsay("Checking distance map move from "
            .. cell_string_from_map_position(current)
            .. " to " .. cell_string_from_map_position(pos))
    end

    if not search.cache[pos.x] then
        search.cache[pos.x] = {}
    end

    local cache_result = search.cache[pos.x][pos.y]
    if cache ~= nil then
        if debug_channel("move-all") then
            dsay("Returning cached result for search")
        end

        if cache_result then
            if not search.first_pos then
                search.first_pos = pos
            end

            search.last_pos = cache_result
        end

        return cache_result
    end

    if positions_equal(current, search.center) then
        search.first_pos = nil
        search.last_pos = nil
    end

    if search.square_func(pos) then
        search.last_pos = pos

        local set_first_pos = not search.first_pos
        if set_first_pos then
            search.first_pos = pos
        end

        if do_distance_map_search(search, pos) then
            search.cache[pos.x][pos.y] = pos
            return true
        else
            if set_first_pos then
                search.first_pos = nil
            end

            search.cache[pos.x][pos.y] = false
            return false
        end
    end

    if debug_channel("move-all") then
        dsay("Square function failed")
    end

    search.cache[pos.x][pos.y] = false
    return false
end

function do_distance_map_search(search, current)
    if position_distance(search.target, current) <= search.min_dist then
        search.move = position_difference(search.first_pos, search.center)
        return true
    end

    local current_dist = search.map[current.x][current.y]
    if not current_dist then
        return false
    end

    for pos in adjacent_iter(current) do
        local dist = search.map[pos.x][pos.y]
        if dist and dist < current_dist then
            if distance_map_search_from(search, pos, current) then
                return true
            end
        end
    end

    return false
end

function distance_map_search(center, target, square_func, min_dist,
        allow_unsafe, cache)
    if not min_dist then
        min_dist = 0
    end

    if position_distance(center, target) <= min_dist then
        return
    end

    if debug_channel("move-all") then
        dsay("Distance map move search from "
            .. cell_string_from_map_position(center)
            .. " to " .. cell_string_from_map_position(target))
    end

    local dist_map = get_distance_map(target)
    local map  = allow_unsafe and dist_map.map or dist_map.excluded_map
    local dist = map[center.x][center.y]
    if not dist then
        return
    end

    search = { center = center, target = target, square_func = square_func,
        min_dist = min_dist, allow_unsafe = allow_unsafe, map = map,
        dist = dist }

    if cache then
        search.cache = cache
    else
        search.cache = { }
    end

    if do_distance_map_search(search, center) then
        return search
    end
end
------------------
-- Plans specific to the Abyss.

function plan_go_to_abyss_portal()
    if unable_to_travel()
            or in_branch("Abyss")
            or goal_branch ~= "Abyss"
            or not branch_found("Abyss") then
        return false
    end

    magicfind("one-way gate to the infinite horrors of the Abyss")
    return true
end

function plan_enter_abyss()
    if view.feature_at(0, 0) == "enter_abyss"
            and goal_branch == "Abyss"
            and not unable_to_use_stairs() then
        go_downstairs(true, true)
        return true
    end

    return false
end

function plan_pick_up_abyssal_rune()
    if not in_branch("Abyss") or have_branch_runes("Abyss") then
        return false
    end

    local rune_pos = item_map_positions[branch_runes(where_branch, true)[1]]
    if rune_pos and positions_equal(qw.map_pos, rune_pos) then
        magic(",")
        return true
    end

    return false
end

function want_to_stay_in_abyss()
    return goal_branch == "Abyss" and not hp_is_low(50)
end

function plan_exit_abyss()
    if view.feature_at(0, 0) == branch_exit("Abyss")
            and not want_to_stay_in_abyss()
            and not unable_to_use_stairs() then
        go_upstairs()
        return true
    end

    return false
end

function plan_lugonu_exit_abyss()
    if not in_branch("Abyss")
            or want_to_stay_in_abyss()
            or you.god() ~= "Lugonu"
            or not can_invoke()
            or you.piety_rank() < 1
            or not can_use_mp(1) then
        return false
    end

    use_ability("Depart the Abyss")
    return true
end

function want_to_move_to_abyss_objective()
    return in_branch("Abyss") and not you.confused() and not hp_is_low(75)
end

function plan_move_towards_abyssal_feature()
    if not want_to_move_to_abyss_objective()
            or unable_to_move()
            or dangerous_to_move() then
        return false
    end

    local feats = goal_travel_features()
    if feats then
        local result = best_move_towards_features(feats, true)
        if result then
            return move_towards_destination(result.move, result.dest, "goal")
        end
    end

    return false
end

function plan_go_down_abyss()
    if in_branch("Abyss")
            and goal_branch == "Abyss"
            and where_depth < goal_depth
            and view.feature_at(0, 0) == "abyssal_stair"
            and not unable_to_use_stairs() then
        go_downstairs()
        return true
    end

    return false
end

function plan_abyss_wait_one_turn()
    if in_branch("Abyss") then
        wait_one_turn()
        return true
    end

    return false
end

function want_to_move_to_abyssal_rune()
    if not want_to_move_to_abyss_objective() or goal_branch ~= "Abyss" then
        return false
    end

    local rune_pos = item_map_positions[branch_runes(where_branch, true)[1]]
    return rune_pos and not positions_equal(qw.map_pos, rune_pos)
        or c_persist.sense_abyssal_rune
end

function plan_move_towards_abyssal_rune()
    if not want_to_move_to_abyssal_rune()
            or unable_to_move()
            or dangerous_to_move() then
        return false
    end

    local rune = branch_runes(where_branch, true)[1]
    local rune_pos = get_item_map_positions({ rune })
    if rune_pos then
        rune_pos = rune_pos[1]
    else
        return false
    end

    local result = best_move_towards(rune_pos, qw.map_pos, true)
    if result then
        return move_towards_destination(result.move, result.rune_pos, "goal")
    end

    result = best_move_towards_unexplored_near(rune_pos, true)
    if result then
        return move_towards_destination(result.move, result.dest, "goal")
    end

    return false
end

function plan_explore_near_runelights()
    if not want_to_move_to_abyss_objective()
            or unable_to_move()
            or dangerous_to_move() then
        return false
    end

    local runelights = get_feature_map_positions({ "runelight" })
    if not runelights then
        return false
    end

    local result = best_move_towards_unexplored_near_positions(runelights)
    if result then
        return move_towards_destination(result.move, result.dest, "goal")
    end

    return false
end
------------------
-- Attack plans
--

function can_attack_invis_at(pos)
    return not is_solid_at(pos) and not get_monster_at(pos)
end

function plan_flail_at_invis()
    if not invis_monster or using_ranged_weapon() or dangerous_to_melee() then
        return false
    end

    local can_ctrl = not you.confused()
    if invis_monster_pos then
        if is_adjacent(invis_monster_pos)
                and can_attack_invis_at(invis_monster_pos) then
            do_melee_attack(invis_monster_pos, can_ctrl)
            return true
        end

        if invis_monster_pos.x == 0 then
            local apos = { x = 0, y = sign(invis_monster_pos.y) }
            if can_attack_invis_at(apos) then
                do_melee_attack(apos, can_ctrl)
                return true
            end
        end

        if invis_monster_pos.y == 0 then
            local apos = { x = sign(invis_monster_pos.x), y = 0 }
            if can_attack_invis_at(apos) then
                do_melee_attack(apos, can_ctrl)
                return true
            end
        end
    end

    local tries = 0
    while tries < 100 do
        local pos = { x = -1 + crawl.random2(3), y = -1 + crawl.random2(3) }
        tries = tries + 1
        if supdist(pos) > 0 and can_attack_invis_at(pos) then
            do_melee_attack(pos, can_ctrl)
            return true
        end
    end

    return false
end

function plan_shoot_at_invis()
    if not invis_monster
            or not using_ranged_weapon()
            or unable_to_shoot()
            or dangerous_to_shoot() then
        return false
    end

    local can_ctrl = not you.confused()
    if invis_monster_pos then
        if player_has_line_of_fire(invis_monster_pos) then
            return shoot_launcher(invis_monster_pos)
        end

        if invis_monster_pos.x == 0 then
            local apos = { x = 0, y = sign(invis_monster_pos.y) }
            if player_has_line_of_fire(apos) then
                return shoot_launcher(apos)
            end
        end

        if invis_monster_pos.y == 0 then
            local apos = { x = sign(invis_monster_pos.x), y = 0 }
            if player_has_line_of_fire(apos) then
                return shoot_launcher(apos)
            end
        end
    end

    local tries = 0
    while tries < 100 do
        local pos = { x = -1 + crawl.random2(3), y = -1 + crawl.random2(3) }
        tries = tries + 1
        if supdist(pos) > 0 and player_has_line_of_fire(pos) then
            return shoot_launcher(pos)
        end
    end

    return false
end

function do_melee_attack(pos, use_control)
    if use_control or you.confused() and you.transform() == "tree" then
        magic(control(delta_to_vi(pos)) .. "Y")
        return
    end

    magic(delta_to_vi(pos) .. "Y")
end

-- This gets stuck if netted, confused, etc
function do_reach_attack(pos)
    magic('vr' .. vector_move(pos) .. '.')
end

function plan_melee()
    if not qw.danger_in_los
            or using_ranged_weapon()
            or unable_to_melee()
            or dangerous_to_melee() then
        return false
    end

    local target = get_melee_target()
    if not target then
        return false
    end

    local enemy = get_monster_at(target.pos)
    if not enemy:player_can_melee() then
        return false
    end

    if enemy:distance() == 1 then
        do_melee_attack(enemy:pos())
    else
        do_reach_attack(enemy:pos())
    end

    return true
end

function plan_launcher()
    if not qw.danger_in_los
            or not using_ranged_weapon()
            or unable_to_shoot()
            or dangerous_to_attack() then
        return false
    end

    local target = get_launcher_target()
    if not target then
        return false
    end

    return shoot_launcher(target.pos, target.aim_at_target)
end

function throw_missile(missile, pos, aim_at_target)
    local cur_missile = items.fired_item()
    if not cur_missile or missile.name() ~= cur_missile.name() then
        magic("Q*" .. item_letter(missile))
        qw.do_dummy_action = false
        coroutine.yield()
    end

    return crawl.do_targeted_command("CMD_FIRE", pos.x, pos.y, aim_at_target)
end

function shoot_launcher(pos, aim_at_target)
    local weapon = get_weapon()
    local cur_missile = items.fired_item()
    if not cur_missile or weapon.name() ~= cur_missile.name() then
        magic("Q*" .. item_letter(weapon))
        qw.do_dummy_action = false
        coroutine.yield()
    end

    return crawl.do_targeted_command("CMD_FIRE", pos.x, pos.y, aim_at_target)
end

function plan_throw()
    if not qw.danger_in_los or unable_to_throw() or dangerous_to_attack() then
        return false
    end

    local target = get_throwing_target()
    if not target then
        return false
    end

    return throw_missile(target.attack.items[1], target.pos,
        target.aim_at_target)
end

function wait_combat()
    last_wait = you.turns()
    wait_count = wait_count + 1
    wait_one_turn()
end

function plan_melee_wait_for_enemy()
    if not qw.danger_in_los or using_ranged_weapon() then
        return false
    end

    if unable_to_move() or dangerous_to_move() then
        wait_combat()
        return true
    end

    if dangerous_to_attack()
            or qw.position_is_cloudy
            or not options.autopick_on
            or view.feature_at(0, 0) == "shallow_water"
                and intrinsic_fumble()
                and not you.flying()
            or in_branch("Abyss")
            or wait_count >= 10 then
        wait_count = 0
        return false
    end

    if you.turns() >= last_wait + 10 then
        wait_count = 0
    end

    -- Hack to wait when we enter the Vaults end, so we don't move off
    -- stairs.
    if vaults_end_entry_turn and you.turns() <= vaults_end_entry_turn + 2 then
        wait_combat()
        return true
    end

    local target = get_melee_target()
    local want_wait = false
    for _, enemy in ipairs(qw.enemy_list) do
        -- We prefer to wait for a target monster to reach us over moving
        -- towards it. However if there exists monsters with ranged attacks,
        -- we prefer to move closer to our target over waiting. This way we
        -- are hit with fewer ranged attacks over time.
        if target and enemy:is_ranged() then
            wait_count = 0
            return false
        end

        if not want_wait and enemy:player_can_wait_for_melee() then
            want_wait = true

            -- If we don't have a target, we'll never abort from waiting due
            -- to ranged monsters, since we can't move towards one anyhow.
            if not target then
                break
            end
        end
    end
    if want_wait then
        wait_combat()
        return true
    end

    return false
end

function plan_launcher_wait_for_enemy()
    if not qw.danger_in_los or not using_ranged_weapon() then
        return false
    end

    if unable_to_move() or dangerous_to_move() then
        wait_combat()
        return true
    end

    if dangerous_to_attack()
            or qw.position_is_cloudy
            or not options.autopick_on
            or view.feature_at(0, 0) == "shallow_water"
                and intrinsic_fumble()
                and not you.flying()
            or in_branch("Abyss")
            or wait_count >= 10 then
        wait_count = 0
        return false
    end

    if you.turns() >= last_wait + 10 then
        wait_count = 0
    end

    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:player_can_wait_for_melee() then
            wait_combat()
            return true
        end
    end

    return false
end

function plan_poison_spit()
    local mut_level = you.mutation("spit poison")
    if not qw.danger_in_los
            or dangerous_to_attack()
            or you.xl() > 11
            or mut_level < 1
            or you.breath_timeout()
            or you.berserk()
            or you.confused() then
        return false
    end

    local range = 5
    local ability = "Spit Poison"
    if mut_level > 1 then
        range = 6
        ability = "Breathe Poison Gas"
    end

    local target = get_ranged_attack_target(poison_spit_attack(),
        not using_ranged_weapon())
    if not target then
        return false
    end

    return use_ability(ability, "r" .. vector_move(target.pos)
        .. (target.aim_at_target and "." or "\r"))
end

function evoke_targeted_item(item, pos, aim_at_target)
    local cur_quiver = items.fired_item()
    local name = item.name()
    if not cur_quiver or name ~= cur_quiver.name() then
        magic("Q*" .. item_letter(item))
        qw.do_dummy_action = false
        coroutine.yield()
    end

    say("EVOKING " .. name .. " at " .. cell_string_from_position(pos) .. ".")
    magic("fr" .. vector_move(pos) .. (aim_at_target and "." or "\r"))
    -- Currently broken when no monsters are available for autotargeting.
    -- return crawl.do_targeted_command("CMD_FIRE", pos.x, pos.y,
    -- aim_at_target)
end

function plan_targeted_evoke()
    if not qw.danger_in_los or dangerous_to_attack() or not can_evoke() then
        return false
    end

    local target = get_evoke_target()
    if not target then
        return false
    end

    evoke_targeted_item(target.attack.items[1], target.pos,
        target.aim_at_target)
end

function plan_flight_move_towards_enemy()
    if not qw.danger_in_los
            or using_ranged_weapon()
            or unable_to_move()
            or dangerous_to_attack()
            or dangerous_to_move() then
        return false
    end

    local potion = find_item("potion", "enlightenment")
    if not potion or not can_drink() then
        return false
    end

    local target = get_melee_target(true)
    if not target then
        return false
    end

    local move = get_monster_at(target.pos):get_player_move_towards(true)
    local feat = view.feature_at(move.x, move.y)
    -- Only quaff flight when we finally reach an impassable square.
    if (feat == "deep_water" or feat == "lava")
            and not is_traversable_at(move) then
        return drink_potion(potion)
    else
        return move_to(move)
    end

    return false
end

function plan_move_towards_enemy()
    if not qw.danger_in_los
            or using_ranged_weapon()
            or unable_to_move()
            or dangerous_to_attack()
            or dangerous_to_move() then
        return false
    end

    local target = get_melee_target()
    if not target then
        return false
    end

    local mons = get_monster_at(target.pos)
    local move = mons:get_player_move_towards()
    if not move then
        return false
    end

    qw.enemy_memory = position_difference(mons:pos(), move)
    qw.enemy_map_memory = position_sum(qw.map_pos, mons:pos())
    qw.enemy_memory_turns_left = 2
    return move_to(move)
end

function closest_adjacent_map_position(map_pos)
    if map_is_reachable_at(map_pos) then
        return pos
    end

    local best_dist, best_pos
    for pos in adjacent_iter(map_pos) do
        local dist = position_distance(pos, qw.map_pos)
        if map_is_reachable_at(pos)
                and (not best_dist or dist < best_dist) then
            best_dist = dist
            best_pos = pos
        end
    end

    return best_pos
end

function plan_continue_move_towards_enemy()
    if not qw.enemy_memory
            or not options.autopick_on
            or unable_to_move()
            or dangerous_to_attack()
            or dangerous_to_move() then
        return false
    end

    if qw.enemy_memory and position_is_origin(qw.enemy_memory) then
        qw.enemy_memory = nil
        qw.enemy_memory_turns_left = 0
        qw.enemy_map_memory = nil
        return false
    end

    if qw.enemy_memory_turns_left > 0 then
        local result = move_search(const.origin, qw.enemy_memory,
            tab_function(), player_reach_range())
        if not result then
            return false
        end

        return move_to(result.move)
    end

    qw.enemy_memory = nil

    if qw.last_enemy_map_memory
            and qw.enemy_map_memory
            and positions_equal(qw.last_enemy_map_memory, qw.enemy_map_memory) then
        qw.enemy_map_memory = nil

        local dest = closest_adjacent_map_position(qw.last_enemy_map_memory)
        if not dest then
            return false
        end

        local result = best_move_towards(dest)
        if result then
            return move_towards_destination(result.move, result.dest,
                "monster")
        end
    end

    qw.last_enemy_map_memory = qw.enemy_map_memory
    qw.enemy_map_memory = nil
    return false
end

function random_step(reason)
    if you.mesmerised() then
        say("Waiting to end mesmerise (" .. reason .. ").")
        wait_one_turn()
        return true
    end

    local new_pos
    local count = 0
    for pos in adjacent_iter(const.origin) do
        if can_move_to(pos, const.origin) then
            count = count + 1
            if crawl.one_chance_in(count) then
                new_pos = pos
            end
        end
    end
    if count > 0 then
        say("Stepping randomly (" .. reason .. ").")
        return move_to(new_pos)
    else
        say("Standing still (" .. reason .. ").")
        wait_one_turn()
        return true
    end
end

function plan_disturbance_random_step()
    if crawl.messages(5):find("There is a strange disturbance nearby!") then
        return random_step("disturbance")
    end
    return false
end

function set_plan_attack()
    plans.attack = cascade {
        {plan_starting_spell, "starting_spell"},
        {plan_poison_spit, "poison_spit"},
        {plan_targeted_evoke, "attack_wand"},
        {plan_throw, "throw"},
        {plan_launcher, "launcher"},
        {plan_melee, "melee"},
        {plan_launcher_wait_for_enemy, "launcher_wait_for_enemy"},
        {plan_melee_wait_for_enemy, "melee_wait_for_enemy"},
        {plan_continue_move_towards_enemy, "continue_move_towards_enemy"},
        {plan_move_towards_enemy, "move_towards_enemy"},
        {plan_flight_move_towards_enemy, "flight_move_towards_enemy"},
        {plan_shoot_at_invis, "shoot_at_invis"},
        {plan_flail_at_invis, "flail_at_invis"},
        {plan_disturbance_random_step, "disturbance_random_step"},
    }
end
------------------
-- Emergency plans

function plan_teleport()
    if can_teleport() and want_to_teleport() then
        return teleport()
    end

    return false
end

-- Are we significantly stronger than usual thanks to a buff that we used?
function buffed()
    if hp_is_low(50)
            or transformed()
            or you.corrosion() >= 8 + qw.base_corrosion then
        return false
    end

    if you.god() == "Okawaru"
            and (have_duration("heroism") or have_duration("finesse")) then
        return true
    end

    if you.extra_resistant() then
        return true
    end

    return false
end

function use_ru_healing()
    use_ability("Draw Out Power")
end

function use_ely_healing()
    use_ability("Heal Self")
end

function use_purification()
    use_ability("Purification")
end

function plan_brothers_in_arms()
    if can_brothers_in_arms() and want_to_brothers_in_arms() then
        return use_ability("Brothers in Arms")
    end

    return false
end

function plan_greater_servant()
    if can_greater_servant() and want_to_greater_servant() then
        return use_ability("Infernal Servant")
    end

    return false
end

function plan_cleansing_flame()
    if can_cleansing_flame() and want_to_cleansing_flame() then
        return use_ability("Cleansing Flame")
    end

    return false
end

function plan_divine_warrior()
    if can_divine_warrior() and want_to_divine_warrior() then
        return use_ability("Summon Divine Warrior")
    end

    return false
end

function plan_recite()
    if can_recite()
            and qw.danger_in_los
            and not (qw.immediate_danger and hp_is_low(33)) then
        return use_ability("Recite", "", true)
    end

    return false
end

function plan_tactical_step()
    if not qw.tactical_step then
        return false
    end

    say("Stepping ~*~*~tactically~*~*~ (" .. qw.tactical_reason .. ").")
    return move_to(qw.tactical_step)
end

function plan_priority_tactical_step()
    if qw.tactical_reason == "cloud"
            or qw.tactical_reason == "sticky flame" then
        return plan_tactical_step()
    end

    return false
end

function plan_flee()
    if unable_to_move() or dangerous_to_move() or not want_to_flee() then
        return false
    end

    local result = get_flee_move()
    if not result then
        return false
    end

    if not qw.danger_in_los then
        qw.last_flee_turn = you.turns()
    end

    if move_to(result.move) then
        say("FLEEEEING towards " .. cell_string_from_map_position(result.dest))
        return true
    end

    return false
end

-- XXX: This plan is broken due to changes to combat assessment.
function plan_grand_finale()
    if not qw.danger_in_los
            or dangerous_to_attack()
            or you.teleporting
            or not can_grand_finale() then
        return false
    end

    local invo = you.skill("Invocations")
    -- fail rate potentially too high, need to add ability failure rate lua
    if invo < 10 or you.piety_rank() < 6 and invo < 15 then
        return false
    end
    local bestx, besty, best_info, new_info
    local flag_order = {"threat", "injury", "distance"}
    local flag_reversed = {false, true, true}
    local best_info, best_pos
    for _, enemy in ipairs(qw.enemy_list) do
        local pos = enemy:pos()
        if is_traversable_at(pos)
                and not cloud_is_dangerous_at(pos) then
            if new_info.safe == 0
                    and (not best_info
                        or compare_melee_targets(enemy, best_enemy, props, reversed)) then
                best_info = new_info
                best_pos = pos
            end
        end
    end
    if best_info then
        use_ability("Grand Finale", "r" .. vector_move(best_pos) .. "\rY")
        return true
    end
    return false
end

function plan_apocalypse()
    if can_apocalypse() and want_to_apocalypse() then
        return use_ability("Apocalypse")
    end

    return false
end

function plan_hydra_destruction()
    if not can_destruction()
            or you.skill("Invocations") < 8
            or check_greater_servants(4) then
        return false
    end

    local hydra_dist = dangerous_hydra_distance()
    if not hydra_dist or hydra_dist > 5 then
        return false
    end

    return use_ability("Unleash Destruction",
        "r" .. vector_move(enemy:x_pos(), enemy:y_pos()) .. "\r")
end

function fiery_armour()
    use_ability("Fiery Armour")
end

function plan_resistance()
    if can_drink() and want_resistance() then
        return drink_by_name("resistance")
    end

    return false
end

function plan_magic_points()
    if can_drink() and want_magic_points() then
        return drink_by_name("magic")
    end

    return false
end

function plan_trogs_hand()
    if can_trogs_hand() and want_to_trogs_hand() then
        return use_ability("Trog's Hand")
    end

    return false
end

function plan_cure_bad_poison()
    if not qw.danger_in_los then
        return false
    end

    if you.poison_survival() <= you.hp() - 60 then
        if drink_by_name("curing") then
            say("(to cure bad poison)")
            return true
        end

        if can_purification() then
            return use_purification()
        end
    end

    return false
end

function plan_cancellation()
    if not qw.danger_in_los or not can_drink() or you.teleporting() then
        return false
    end

    if you.petrifying()
            or you.corrosion() >= 16 + qw.base_corrosion
            or you.corrosion() >= 12 + qw.base_corrosion and hp_is_low(70)
            or in_bad_form() then
        return drink_by_name("cancellation")
    end

    return false
end

function plan_blinking()
    if not in_branch("Zig") or not qw.danger_in_los or not can_read() then
        return false
    end

    local para_danger = false
    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:name() == "floating eye"
                or enemy:name() == "starcursed mass" then
            para_danger = true
        end
    end
    if not para_danger then
        return false
    end

    if count_item("scroll", "blinking") == 0 then
        return false
    end

    local cur_count = 0
    for pos in adjacent_iter(const.origin) do
        local mons = get_monster_at(pos)
        if mons and mons:name() == "floating eye" then
            cur_count = cur_count + 3
        elseif mons and mons:name() == "starcursed mass" then
            cur_count = cur_count + 1
        end
    end
    if cur_count >= 2 then
        return false
    end

    local best_count = 0
    local best_pos
    for pos in square_iter(const.origin) do
        if is_traversable_at(pos)
                and not is_solid_at(pos)
                and not get_monster_at(pos)
                and is_safe_at(pos)
                and not view.withheld(pos.x, pos.y)
                and you.see_cell_no_trans(pos.x, pos.y) then
            local count = 0
            for dpos in adjacent_iter(pos) do
                if supdist(dpos) <= qw.los_radius then
                    local mons = get_monster_at(dpos)
                    if mons and mons:is_enemy()
                            and mons:name() == "floating eye" then
                        count = count + 3
                    elseif mons
                            and mons:is_enemy()
                            and mons:name() == "starcursed mass" then
                        count = count + 1
                    end
                end
            end
            if count > best_count then
                best_count = count
                best_pos = pos
            end
        end
    end
    if best_count >= cur_count + 2 then
        local scroll = find_item("scroll", "blinking")
        return read_scroll(scroll,  vector_move(best_x, best_y) .. ".")
    end
    return false
end

function can_drink_heal_wounds()
    if not can_drink()
            or not find_item("potion", "heal wounds")
            or you.mutation("no potion heal") > 1 then
        return false
    end

    local armour = get_slot_item("body")
    if armour and armour:name():find("NoPotionHeal") then
        return false
    end

    return true
end

function heal_general()
    if can_ru_healing() and drain_level() <= 1 then
        return use_ru_healing()
    end

    if can_ely_healing() then
        return use_ely_healing()
    end

    if can_drink_heal_wounds() then
        if drink_by_name("heal wounds") then
            return true
        elseif not item_type_is_ided("potion", "heal wounds")
                and quaff_unided_potion() then
            return true
        end
    end

    if can_ru_healing() then
        return use_ru_healing()
    end

    if can_ely_healing() then
        return use_ely_healing()
    end

    return false
end

function plan_heal_wounds()
    if want_to_heal_wounds() then
        return heal_general()
    end

    return false
end

function can_haste()
    return can_drink()
        and not you.berserk()
        and you.god() ~= "Cheibriados"
        and you.race() ~= "Formicid"
        and find_item("potion", "haste")
end

function plan_haste()
    if can_haste() and want_to_haste() then
        return drink_by_name("haste")
    end

    return false
end

function can_might()
    return can_drink() and find_item("potion", "might")
end

function want_to_might()
    if not danger
            or dangerous_to_attack()
            or you.mighty()
            or you.teleporting()
            or will_kite() then
        return false
    end

    local result = assess_enemies()
    if result.threat >= high_threat_level() then
        return true
    elseif result.scary_enemy then
        attack = result.scary_enemy:best_player_attack()
        return attack and attack.uses_might
    end

    return false
end

function plan_might()
    if can_might() and want_to_might() then
        return drink_by_name("might")
    end

    return false
end

function plan_berserk()
    if can_berserk() and want_to_berserk() then
        return use_ability("Berserk")
    end

    return false
end

function plan_heroism()
    if can_heroism() and want_to_heroism() then
        return use_ability("Heroism")
    end

    return false
end

function plan_recall()
    if can_recall() and want_to_recall() then
        if you.god() == "Yredelemnul" then
            use_ability("Recall Undead Harvest", "", true)
        else
            use_ability("Recall Apostles", "", true)
        end
    end

    return false
end

function plan_recall_ancestor()
    if can_recall_ancestor() and check_elliptic(qw.los_radius) then
        return use_ability("Recall Ancestor", "", true)
    end

    return false
end

function plan_finesse()
    if can_finesse() and want_to_finesse() then
        return use_ability("Finesse")
    end

    return false
end

function plan_slouch()
    if can_slouch() and want_to_slouch() then
        return use_ability("Slouch")
    end

    return false
end

function plan_drain_life()
    -- The Yredelemnul rework in DCSS 0.33 removed the "Drain Life" ability,
    -- so this plan no longer does anything.
    return false
end

function plan_fiery_armour()
    if can_fiery_armour() and want_to_fiery_armour() then
        return use_ability("Fiery Armour")
    end

    return false
end

function want_to_brothers_in_arms()
    if not qw.danger_in_los
            or dangerous_to_attack()
            or you.teleporting()
            or check_brothers_in_arms(4) then
        return false
    end

    -- If threat is too high even with any available buffs like berserk.
    local result = assess_enemies(const.duration.available)
    if result.threat >= 15 then
        return true
    end

    return false
end

function want_to_slouch()
    return qw.danger_in_los
        and not dangerous_to_attack()
        and not you.teleporting()
        and you.piety_rank() == 6
        and estimate_slouch_damage() >= 6
end

function want_to_greater_servant()
    if not qw.danger_in_los
            or dangerous_to_attack()
            or you.teleporting()
            or you.skill("Invocations") < 12
            or check_greater_servants(4) then
        return false
    end

    if hp_is_low(50) and qw.immediate_danger then
        return true
    end

    local result = assess_enemies()
    if result.threat >= 15 then
        return true
    end

    return false
end

function want_to_cleansing_flame()
    if not qw.danger_in_los or dangerous_to_attack() then
        return false
    end

    local result = assess_enemies(const.duration.active, 2,
        function(mons) return mons:res_holy() <= 0 end)
    if result.scary_enemy and not result.scary_enemy:player_can_attack(1)
            or result.threat >= high_threat_level() and result.count >= 3 then
        return true
    end

    if hp_is_low(50) and qw.immediate_danger then
        local flame_restore_count = count_enemies(2, mons_tso_heal_check)
        return flame_restore_count > count_enemies(1, mons_tso_heal_check)
            and flame_restore_count >= 4
    end

    return false
end

function want_to_divine_warrior()
    if not qw.danger_in_los
            or dangerous_to_attack()
            or you.teleporting()
            or you.skill("Invocations") < 8
            or check_divine_warriors(4) then
        return false
    end

    if hp_is_low(50) and qw.immediate_danger then
        return true
    end

    local result = assess_enemies()
    if result.threat >= 15 then
        return true
    end
end

function want_to_fiery_armour()
    if not qw.danger_in_los
            or dangerous_to_attack()
            or you.status("fiery-armoured") then
        return false
    end

    if hp_is_low(50) and qw.immediate_danger then
        return true
    end

    local result = assess_enemies()
    if result.scary_enemy or result.threat >= high_threat_level() then
        return true
    end

    return false
end

function want_to_apocalypse()
    if not qw.danger_in_los or dangerous_to_attack() or you.teleporting() then
        return false
    end

    local dlevel = drain_level()
    local result = assess_enemies()
    if dlevel == 0
                and (result.scary_enemy
                    or result.threat >= high_threat_level())
            or dlevel <= 2 and hp_is_low(50) then
        return true
    end

    return false
end

function bad_corrosion()
    if you.corrosion() == qw.base_corrosion then
        return false
    elseif in_branch("Slime") then
        return you.corrosion() >= 24 + qw.base_corrosion and hp_is_low(70)
    else
        return you.corrosion() >= 12 + qw.base_corrosion and hp_is_low(50)
            or you.corrosion() >= 16 + qw.base_corrosion and hp_is_low(70)
    end
end

function want_to_teleport()
    if you.teleporting() or in_branch("Zig") then
        return false
    end

    if in_bad_form() and not will_flee() then
        return true
    end

    if qw.have_orb and hp_is_low(33) and check_enemies(2) then
        return true
    end

    if count_hostile_summons(qw.los_radius) > 0 and you.xl() < 21 then
        hostile_summons_timer = you.turns()
        return true
    end

    if qw.immediate_danger and bad_corrosion()
            or qw.immediate_danger and hp_is_low(25) then
            return true
    end

    if will_flee() then
        return false
    end

    local enemies = assess_enemies(const.duration.available)
    if enemies.scary_enemy
            and enemies.scary_enemy:threat(const.duration.available) >= 5
            and enemies.scary_enemy:name():find("slime creature")
            and enemies.scary_enemy:name() ~= "slime creature" then
        return true
    end

    if enemies.threat >= extreme_threat_level() then
        return not will_fight_extreme_threat()
    end

    return false
end

function want_to_heal_wounds()
    if want_to_orbrun_heal_wounds() then
        return true
    end

    if not qw.danger_in_los then
        return false
    end

    if can_ely_healing() and hp_is_low(50) and you.piety_rank() >= 5 then
        return true
    end

    return hp_is_low(25)
end

function want_resistance()
    if not qw.danger_in_los
            or dangerous_to_attack()
            or you.teleporting()
            or you.extra_resistant() then
        return false
    end

    for _, enemy in ipairs(qw.enemy_list) do
        if (enemy:has_path_to_melee_player() or enemy:is_ranged(true))
                and (monster_in_list(enemy, fire_resistance_monsters)
                        and you.res_fire() < 3
                    or monster_in_list(enemy, cold_resistance_monsters)
                        and you.res_cold() < 3
                    or monster_in_list(enemy, elec_resistance_monsters)
                        and you.res_shock() < 1
                    or monster_in_list(enemy, pois_resistance_monsters)
                        and you.res_poison() < 1
                    or in_branch("Zig")
                        and monster_in_list(enemy, acid_resistance_monsters)
                        and not you.res_corr()) then
            return true
        end
    end

    return false
end

function want_to_haste()
    if not qw.danger_in_los
            or dangerous_to_attack()
            or you.hasted()
            or you.teleporting()
            or will_kite() then
        return false
    end

    local result = assess_enemies()
    if result.threat >= high_threat_level() then
        return not duration_active("finesse") or you.slowed()
    elseif result.scary_enemy then
        local attack = result.scary_enemy:best_player_attack()
        return attack
            -- We can always use haste if we're slowed().
            and (you.slowed()
                -- Only primary attacks are allowed to use haste.
                or attack.index == 1
                    -- Don't haste if we're already benefiting from Finesse.
                    and not (attack.uses_finesse and duration_active("finesse")))
    end

    return false
end

function want_magic_points()
    if you.race() == "Djinni" then
        return false
    end

    local mp, mmp = you.mp()
    return qw.danger_in_los
        and not dangerous_to_attack()
        and not you.teleporting()
        -- Don't bother restoring MP if our max MP is low.
        and mmp >= 20
        -- No point trying to restore MP with ghost moths around.
        and count_enemies_by_name(qw.los_radius, "ghost moth") == 0
        -- We want and could use these abilities if we had more MP.
        and (can_cleansing_flame(true)
                and not can_cleansing_flame()
                and want_to_cleansing_flame()
            or can_divine_warrior(true)
                and not can_divine_warrior()
                and want_to_divine_warrior())
end

function want_to_trogs_hand()
    if you.regenerating() or you.teleporting() then
        return false
    end

    local hp, mhp = you.hp()
    return in_branch("Abyss") and mhp - hp >= 30
        or not dangerous_to_attack()
            and check_enemies_in_list(qw.los_radius, hand_monsters)
end

function check_berserkable_enemies()
    local filter = function(enemy, moveable)
        return enemy:player_has_path_to_melee()
    end
    return check_enemies(2, filter)
end

function want_to_berserk()
    if not qw.danger_in_los or dangerous_to_melee() or you.berserk() then
        return false
    end

    if hp_is_low(50) and check_berserkable_enemies()
            or invis_monster and nasty_invis_caster then
        return true
    end

    local result = assess_enemies(const.duration.available, 2)
    if result.scary_enemy then
        local attack = result.scary_enemy:best_player_attack()
        if attack and attack.uses_berserk then
            return true
        end
    end

    if result.threat >= high_threat_level() then
        return true
    end

    return false
end

function want_to_finesse()
    if not qw.danger_in_los
            or dangerous_to_attack()
            or duration_active("finesse")
            or you.teleporting()
            or will_kite() then
        return false
    end

    local result = assess_enemies()
    if result.threat >= high_threat_level() then
        return true
    elseif result.scary_enemy then
        attack = result.scary_enemy:best_player_attack()
        return attack and attack.uses_finesse
    end

    return false
end

function want_to_heroism()
    if not qw.danger_in_los
            or dangerous_to_attack()
            or duration_active("heroism")
            or you.teleporting()
            or will_kite() then
        return false
    end

    local result = assess_enemies()
    if result.threat >= high_threat_level() then
        return true
    elseif result.scary_enemy then
        local attack = result.scary_enemy:best_player_attack()
        return attack and attack.uses_heroism
    end

    return false
end

function want_to_recall()
    if qw.immediate_danger and hp_is_low(66) then
        return false
    end

    if you.race() == "Djinni" then
        local hp, mhp = you.hp()
        return hp == mhp
    else
        local mp, mmp = you.mp()
        return mp == mmp
    end
end

function plan_full_inventory_panic()
    if qw.danger_in_los or not qw.position_is_safe then
        return false
    end

    if qw_full_inventory_panic and free_inventory_slots() == 0 then
        panic("Inventory is full!")
    else
        return false
    end
end

function plan_cure_confusion()
    if not you.confused()
            or not can_drink()
            or not (qw.danger_in_los
                or options.autopick_on
                or qw.position_is_cloudy)
            or view.cloud_at(0, 0) == "noxious fumes"
                and not meph_immune() then
        return false
    end

    if drink_by_name("curing") then
        say("(to cure confusion)")
        return true
    end

    if can_purification() then
        return use_purification()
    end

    if not item_type_is_ided("potion", "curing") then
        return quaff_unided_potion()
    end

    return false
end

-- This plan is necessary to make launcher qw try to escape from the net so
-- that it can resume attacking instead of trying post-attack plans. It should
-- come after any emergency plans that we could still execute while caught.
function plan_escape_net()
    if not qw.danger_in_los or not you.caught() then
        return false
    end

    -- Can move in any direction to escape nets, regardless of what's there.
    return move_to({ x = 0, y = 1 })
end

function plan_wait_confusion()
    if not you.confused()
            or not (qw.danger_in_los or options.autopick_on)
            or qw.position_is_cloudy then
        return false
    end

    wait_one_turn()
    return true
end

function plan_non_melee_berserk()
    if not you.berserk() or not using_ranged_weapon() then
        return false
    end

    if unable_to_move() or dangerous_to_move() then
        wait_one_turn()
        return true
    end

    local result = best_move_towards_positions(qw.flee_positions)
    if result then
        return move_to(result.move)
    end

    wait_one_turn()
    return true
end

-- Curing poison/confusion with purification is handled elsewhere.
function plan_special_purification()
    if not can_purification() then
        return false
    end

    if you.slowed() and not qw.slow_aura or you.petrifying() then
        return use_purification()
    end

    local str, mstr = you.strength()
    local int, mint = you.intelligence()
    local dex, mdex = you.dexterity()
    if str < mstr
            and (str < mstr - 5 or str < 3)
                or int < mint and int < 3
                or dex < mdex and (dex < mdex - 8 or dex < 3) then
        return use_purification()
    end

    return false
end

function can_dig_to(pos)
    local positions = spells.path("Dig", pos.x, pos.y, false)
    local hit_grate = false
    for i, coords in ipairs(positions) do
        local dpos = { x = coords[1], y = coords[2] }
        if not hit_grate
                and view.feature_at(dpos.x, dpos.y) == "iron_grate" then
            hit_grate = true
        end

        if positions_equal(pos, dpos) then
            return hit_grate
        end
    end
    return false
end

function plan_tomb2_arrival()
    if not tomb2_entry_turn
            or you.turns() >= tomb2_entry_turn + 5
            or c_persist.did_tomb2_buff then
        return false
    end

    if not you.hasted() then
        return haste()
    elseif not you.status("attractive") then
        if drink_by_name("attraction") then
            c_persist.did_tomb2_buff = true
            return true
        end

        return false
    end
end

function plan_tomb3_arrival()
    if not tomb3_entry_turn
            or you.turns() >= tomb3_entry_turn + 5
            or c_persist.did_tomb3_buff then
        return false
    end

    if not you.hasted() then
        return haste()
    elseif not you.status("attractive") then
        if drink_by_name("attraction") then
            c_persist.did_tomb3_buff = true
            return true
        end

        return false
    end
end

function plan_dig_grate()
    local wand = find_item("wand", "digging")
    if not wand or not can_evoke() then
        return false
    end

    for _, enemy in ipairs(qw.enemy_list) do
        if not map_is_reachable_at(enemy:map_pos())
                and enemy:should_dig_unreachable() then
            return evoke_targeted_item(wand, enemy:pos())
        end
    end

    return false
end

function set_plan_emergency()
    plans.emergency = cascade {
        {plan_stairdance_up, "stairdance_up"},
        {plan_lugonu_exit_abyss, "lugonu_exit_abyss"},
        {plan_exit_abyss, "exit_abyss"},
        {plan_go_down_abyss, "go_down_abyss"},
        {plan_pick_up_rune, "pick_up_rune"},
        {plan_special_purification, "special_purification"},
        {plan_cure_confusion, "cure_confusion"},
        {plan_cancellation, "cancellation"},
        {plan_teleport, "teleport"},
        {plan_remove_terrible_rings, "remove_terrible_rings"},
        {plan_cure_bad_poison, "cure_bad_poison"},
        {plan_blinking, "blinking"},
        {plan_drain_life, "drain_life"},
        {plan_heal_wounds, "heal_wounds"},
        {plan_trogs_hand, "trogs_hand"},
        {plan_escape_net, "escape_net"},
        {plan_move_towards_abyssal_rune, "move_towards_abyssal_rune"},
        {plan_move_towards_abyssal_feature, "move_towards_abyssal_feature"},
        {plan_explore_near_runelights, "explore_near_runelights"},
        {plan_priority_tactical_step, "priority_tactical_step"},
        {plan_wait_confusion, "wait_confusion"},
        {plan_zig_fog, "zig_fog"},
        {plan_flee, "flee"},
        {plan_tactical_step, "tactical_step"},
        {plan_tomb2_arrival, "tomb2_arrival"},
        {plan_tomb3_arrival, "tomb3_arrival"},
        {plan_magic_points, "magic_points"},
        {plan_cleansing_flame, "try_cleansing_flame"},
        {plan_divine_warrior, "divine_warrior"},
        {plan_brothers_in_arms, "brothers_in_arms"},
        {plan_greater_servant, "greater_servant"},
        {plan_apocalypse, "try_apocalypse"},
        {plan_slouch, "try_slouch"},
        {plan_hydra_destruction, "try_hydra_destruction"},
        {plan_grand_finale, "grand_finale"},
        {plan_fiery_armour, "fiery_armour"},
        {plan_dig_grate, "try_dig_grate"},
        {plan_wield_weapon, "wield_weapon"},
        {plan_resistance, "resistance"},
        {plan_finesse, "finesse"},
        {plan_heroism, "heroism"},
        {plan_haste, "haste"},
        {plan_might, "might"},
        {plan_recall, "recall"},
        {plan_recall_ancestor, "try_recall_ancestor"},
        {plan_recite, "try_recite"},
        {plan_berserk, "berserk"},
    }
end
------------------
-- The exploration plan cascades.

function plan_move_towards_safety()
    if autoexplored_level(where_branch, where_depth)
            or disable_autoexplore
            or qw.position_is_safe
            or unable_to_move()
            or dangerous_to_move()
            or you.mesmerised() then
        return false
    end

    local result = best_move_towards_safety()
    if result then
        if debug_channel("move") then
            dsay("Moving to safe position at "
                .. cell_string_from_map_position(result.dest))
        end
        return move_towards_destination(result.move, result.dest, "safety")
    end

    return false
end

function plan_autoexplore()
    if unable_to_travel()
            or disable_autoexplore
            or free_inventory_slots() == 0 then
        return false
    end

    magic("o")
    return true
end

function send_travel(branch, depth)
    local depth_str
    if depth == nil or branch_depth(branch) == 1 then
        depth_str = ""
    else
        depth_str = depth
    end

    magic("G" .. branch_travel(branch) .. depth_str .. "\rY")
end

function unable_to_travel()
    return qw.danger_in_los or qw.position_is_cloudy or unable_to_move()
end

function plan_go_to_portal_entrance()
    if unable_to_travel()
            or in_portal()
            or not is_portal_branch(goal_branch)
            or not branch_found(goal_branch) then
        return false
    end

    local desc = portal_entrance_description(goal_branch)
    -- For timed bazaars, make a search string that can' match permanent
    -- ones.
    if goal_branch == "Bazaar" and not permanent_bazaar then
        desc = "a flickering " .. desc
    end
    magicfind(desc)
    return true
end

-- Use the 'G' command to travel to our next destination.
function plan_go_command()
    if unable_to_travel() or not goal_travel.want_go then
        return false
    end

    -- We can't set goal_travel data to an invalid level like D:0, so we set it
    -- to D:1 and override it in this plan.
    if goal_status == "Escape"
            and goal_travel.branch == "D"
            and goal_travel.depth == 1 then
        -- We're already on the stairs, so travel won't take us further.
        if view.feature_at(0, 0) == branch_exit("D") then
            go_upstairs(true)
        else
            send_travel("D", 0)
        end
    else
        send_travel(goal_travel.branch, goal_travel.depth)
    end
    return true
end

function plan_go_to_portal_exit()
    -- Zig has its own stair handling in plan_zig_go_to_stairs().
    if unable_to_travel() or not in_portal() or where_branch == "Zig" then
        return false
    end

    magic("X<\r")
    return true
end

-- Open runed doors in Pan to get to the pan lord vault and open them on levels
-- that are known to contain entrances to Pan if we intend to visit Pan.
function plan_open_runed_doors()
    if not open_runed_doors then
        return false
    end

    for pos in adjacent_iter(const.origin) do
        if view.feature_at(pos.x, pos.y) == "runed_clear_door" then
            magic(delta_to_vi(pos) .. "Y")
            return true
        end
    end
    return false
end

function plan_enter_portal()
    if not is_portal_branch(goal_branch)
            or view.feature_at(0, 0) ~= branch_entrance(goal_branch)
            or unable_to_use_stairs() then
        return false
    end

    go_downstairs(goal_branch == "Zig", true)
    return true
end

function plan_exit_portal()
    if not in_portal()
            -- Zigs have their own exit rules.
            or where_branch == "Zig"
            or view.feature_at(0, 0) ~= branch_exit(where_branch)
            or unable_to_use_stairs() then
        return false
    end

    local parent, depth = parent_branch(where_branch)
    remove_portal(make_level(parent, depth), where_branch, true)

    go_upstairs()
    return true
end

function want_rune_on_current_level()
    return not have_branch_runes(where_branch)
            and where_branch == goal_branch
            and where_depth == goal_depth
            and goal_depth == branch_rune_depth(goal_branch)
end

function plan_pick_up_rune()
    if not want_rune_on_current_level() then
        return false
    end

    local runes = branch_runes(where_branch, true)
    local rune_positions = get_item_map_positions(runes)
    if not rune_positions
            or not positions_equal(qw.map_pos, rune_positions[1]) then
        return false
    end

    magic(",")
    return true
end

function plan_move_towards_rune()
    if not want_rune_on_current_level()
            or you.confused()
            or unable_to_move()
            or dangerous_to_move() then
        return false
    end

    local runes = branch_runes(where_branch, true)
    local rune_positions = get_item_map_positions(runes)
    if not rune_positions then
        return false
    end

    local result = best_move_towards_positions(rune_positions, true)
    if result then
        return move_towards_destination(result.move, result.dest, "goal")
    end

    return false
end

function plan_move_towards_travel_feature()
    if unable_to_move() or dangerous_to_move() then
        return false
    end

    if goal_travel.safe_hatch and not goal_travel.want_go then
        local map_pos = unhash_position(goal_travel.safe_hatch)
        local result = best_move_towards(map_pos)
        if result then
            return move_towards_destination(result.move, result.des, "goal")
        end

        return false
    end

    local feats = goal_travel_features()
    if not feats then
        return false
    end

    if util.contains(feats, view.feature_at(0, 0)) then
        return false
    end

    local result = best_move_towards_features(feats, true)
    if result then
        return move_towards_destination(result.move, result.dest, "goal")
    end

    local god = goal_god(goal_status)
    if not god then
        return false
    end

    if c_persist.altars[god] and c_persist.altars[god][where] then
        for hash, _ in pairs(c_persist.altars[god][where]) do
            if update_altar(god, where, hash, { feat = const.explore.seen },
                    true) then
                qw.restart_cascade = true
            end
        end
    end

    -- If we're restarting the cascade, we have to do the goal update ourself
    -- to ensure earlier plans have current goal information.
    if qw.restart_cascade and qw.want_goal_update then
        update_goal()
    end

    return false
end

function plan_move_towards_destination()
    if not qw.move_destination or unable_to_move() or dangerous_to_move() then
        return false
    end

    result = best_move_towards(qw.move_destination, qw.map_pos, true)
    if result then
        return move_to(result.move)
    end

    return false
end

function plan_move_towards_monster()
    if not qw.position_is_safe or unable_to_move() or dangerous_to_move() then
        return false
    end

    local mons_targets = {}
    for _, enemy in ipairs(qw.enemy_list) do
        table.insert(mons_targets, position_sum(qw.map_pos, enemy:pos()))
    end

    if #mons_targets == 0 then
        for pos in square_iter(const.origin, qw.los_radius) do
            local mons = monster.get_monster_at(pos.x, pos.y)
            if mons and Monster:new(mons):is_enemy() then
                table.insert(mons_targets, position_sum(qw.map_pos, pos))
            end
        end
    end

    if #mons_targets == 0 then
        return false
    end

    local result = best_move_towards_positions(mons_targets)
    if result then
        if debug_channel("move") then
            dsay("Moving to enemy at "
                .. cell_string_from_map_position(result.dest))
        end
        return move_towards_destination(result.move, result.dest, "monster")
    end

    return false
end

function plan_move_towards_unexplored()
    if disable_autoexplore or unable_to_move() or dangerous_to_move() then
        return false
    end

    local result = best_move_towards_unexplored()
    if result then
        if debug_channel("move") then
            dsay("Moving to explore near safe position at "
                .. cell_string_from_map_position(result.dest))
        end
        return move_towards_destination(result.move, result.dest, "unexplored")
    end

    local result = best_move_towards_unexplored(true)
    if result then
        if debug_channel("move") then
            dsay("Moving to explore near unsafe position at "
                .. cell_string_from_map_position(result.dest))
        end

        return move_towards_destination(result.move, result.dest, "unexplored")
    end

    return false
end

function plan_tomb_use_hatch()
    if (where == "Tomb:2" and not have_branch_runes("Tomb")
                or where == "Tomb:1")
            and view.feature_at(0, 0) == "escape_hatch_down" then
        prev_hatch_dist = 1000
        go_downstairs()
        return true
    end

    if (where == "Tomb:3" and have_branch_runes("Tomb")
                or where == "Tomb:2")
            and view.feature_at(0, 0) == "escape_hatch_up" then
        prev_hatch_dist = 1000
        go_upstairs()
        return true
    end

    return false
end

function plan_tomb_go_to_final_hatch()
    if where == "Tomb:2"
            and not have_branch_runes("Tomb")
            and view.feature_at(0, 0) ~= "escape_hatch_down" then
        magic("X>\r")
        return true
    end
    return false
end

function plan_tomb_go_to_hatch()
    if where == "Tomb:3"
            and have_branch_runes("Tomb")
            and view.feature_at(0, 0) ~= "escape_hatch_up" then
        magic("X<\r")
        return true
    elseif where == "Tomb:2" then
        if not have_branch_runes("Tomb")
                and view.feature_at(0, 0) == "escape_hatch_down" then
            return false
        end

        if view.feature_at(0, 0) == "escape_hatch_up" then
            local new_hatch_dist = supdist(qw.map_pos)
            if new_hatch_dist >= prev_hatch_dist
                    and not positions_equal(qw.map_pos, prev_hatch) then
                return false
            end

            prev_hatch_dist = new_hatch_dist
            prev_hatch = util.copy_table(qw.map_pos)
        end

        magic("X<\r")
        return true
    elseif where == "Tomb:1" then
        if view.feature_at(0, 0) == "escape_hatch_down" then
            local new_hatch_dist = supdist(qw.map_pos)
            if new_hatch_dist >= prev_hatch_dist
                    and not positions_equal(qw.map_pos, prev_hatch) then
                return false
            end

            prev_hatch_dist = new_hatch_dist
            prev_hatch = util.copy_table(qw.map_pos)
        end

        magic("X>\r")
        return true
    end

    return false
end


function set_plan_pre_explore()
    plans.pre_explore = cascade {
        {plan_ancestor_life, "ancestor_life"},
        {plan_sacrifice, "sacrifice"},
        {plans.acquirement, "acquirement"},
        {plan_bless_weapon, "bless_weapon"},
        {plan_remove_shield, "remove_shield"},
        {plan_upgrade_weapon, "upgrade_weapon"},
        {plan_wear_shield, "wear_shield"},
        {plan_use_good_consumables, "use_good_consumables"},
        {plan_unwield_weapon, "unwield_weapon"},
    }
end

function set_plan_explore()
    plans.explore = cascade {
        {plan_dive_pan, "dive_pan"},
        {plan_dive_go_to_pan_downstairs, "try_dive_go_to_pan_downstairs"},
        {plan_move_towards_destination, "move_towards_destination"},
        {plan_take_escape_hatch, "take_escape_hatch"},
        {plan_move_towards_escape_hatch, "try_go_to_escape_hatch"},
        {plan_move_towards_safety, "move_towards_safety"},
        {plan_autoexplore, "try_autoexplore"},
    }
end

function set_plan_pre_explore2()
    plans.pre_explore2 = cascade {
        {plan_upgrade_equipment, "upgrade_equipment"},
        {plan_remove_equipment, "remove_equipment"},
        {plan_use_identify_scrolls, "use_identify_scrolls"},
        {plan_read_unided_scrolls, "try_read_unided_scrolls"},
        {plan_quaff_unided_potions, "quaff_unided_potions"},
        {plan_drop_items, "drop_items"},
        {plan_full_inventory_panic, "full_inventory_panic"},
    }
end

function set_plan_explore2()
    plans.explore2 = cascade {
        {plan_abandon_god, "abandon_god"},
        {plan_use_altar, "use_altar"},
        {plan_go_to_altar, "try_go_to_altar"},
        {plan_enter_portal, "enter_portal"},
        {plan_go_to_portal_entrance, "try_go_to_portal_entrance"},
        {plan_open_runed_doors, "open_runed_doors"},
        {plan_enter_transporter, "enter_transporter"},
        {plan_transporter_orient_exit, "try_transporter_orient_exit"},
        {plan_go_to_transporter, "try_go_to_transporter"},
        {plan_exit_portal, "exit_portal"},
        {plan_go_to_portal_exit, "try_go_to_portal_exit"},
        {plan_shopping_spree, "try_shopping_spree"},
        {plan_tomb_go_to_final_hatch, "try_tomb_go_to_final_hatch"},
        {plan_tomb_go_to_hatch, "try_tomb_go_to_hatch"},
        {plan_tomb_use_hatch, "tomb_use_hatch"},
        {plan_enter_pan, "enter_pan"},
        {plan_go_to_pan_portal, "try_go_to_pan_portal"},
        {plan_exit_pan, "exit_pan"},
        {plan_go_to_pan_exit, "try_go_to_pan_exit"},
        {plan_go_down_pan, "try_go_down_pan"},
        {plan_go_to_pan_downstairs, "try_go_to_pan_downstairs"},
        {plan_enter_abyss, "enter_abyss"},
        {plan_go_to_abyss_portal, "try_go_to_abyss_portal"},
        {plan_move_to_zigfig_location, "try_move_to_zigfig_location"},
        {plan_use_zigfig, "use_zigfig"},
        {plan_zig_dig, "zig_dig"},
        {plan_go_to_zig_dig, "try_go_to_zig_dig"},
        {plan_zig_leave_level, "zig_leave_level"},
        {plan_zig_go_to_stairs, "try_zig_go_to_stairs"},
        {plan_take_unexplored_stairs, "take_unexplored_stairs"},
        {plan_go_to_unexplored_stairs, "try_go_to_unexplored_stairs"},
        {plan_move_towards_rune, "move_towards_rune"},
        {plan_go_to_orb, "try_go_to_orb"},
        {plan_go_command, "try_go_command"},
        {plan_teleport_dangerous_stairs, "teleport_dangerous_stairs"},
        {plan_use_travel_stairs, "use_travel_stairs"},
        {plan_move_towards_travel_feature, "move_towards_travel_feature"},
        {plan_autoexplore, "try_autoexplore2"},
        {plan_move_towards_monster, "move_towards_monster"},
        {plan_move_towards_unexplored, "move_towards_unexplored"},
        {plan_unexplored_stairs_backtrack, "try_unexplored_stairs_backtrack"},
        {plan_abort_safe_stairs, "try_abort_safe_stairs"},
    }
end
------------------
-- Plans for using items, including the acquirement plan cascade.

function read_scroll(item, etc)
    if not etc then
        etc = ""
    end

    say("READING " .. item.name() .. ".")
    magic("r" .. item_letter(item) .. etc)
end

function read_scroll_by_name(name, etc)
    local item = find_item("scroll", name)
    if item then
        read_scroll(item, etc)
        return true
    end

    return false
end

function drink_potion(item)
    say("DRINKING " .. item.name() .. ".")
    magic("q" .. item_letter(item))
end

function drink_by_name(name)
    local potion = find_item("potion", name)
    if potion then
        drink_potion(potion)
        return true
    end

    return false
end

function teleport()
    return read_scroll_by_name("teleportation")
end

function dangerous_hydra_distance(ignore_weapon)
    if you.xl() >= 18 and (ignore_weapon or hydra_melee_value() > 0) then
        return
    end

    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:is_real_hydra() then
            return enemy:distance()
        end
    end
end

function best_hydra_swap_weapon()
    local best_weapon, best_value
    local cur_weapons = inventory_equip(const.inventory.equipped).weapon
    for weapon in inventory_slot_iter("weapon") do
        if weapon.equipped or equip_letter_for_item(weapon, "weapon") then
            local value = equip_value(weapon, true, cur_weapons, "hydra")
            if value > 0 and (not best_value or value > best_value) then
                best_weapon = weapon
                best_value = value
            end
        end
    end
    return best_weapon
end

function plan_wield_weapon()
    if unable_to_swap_weapons() then
        return false
    end

    local hydra_dist = dangerous_hydra_distance(true)
    if hydra_dist and hydra_dist <= 2 then
        return equip_item(best_hydra_swap_weapon(), "weapon")
    end

    local best_equip = best_equip_set()
    for weapon in equip_set_slot_iter(best_equip, "weapon") do
        if equip_item(weapon, "weapon", best_equip) then
            return true
        end
    end

    return false
end

function plan_bless_weapon()
    if you.god() ~= "the Shining One"
            or you.one_time_ability_used()
            or you.piety_rank() < 6
            or not can_invoke() then
        return false
    end

    local cur_equip = inventory_equip(const.inventory.equipped)
    local best_weapon, best_value
    for weapon in inventory_slot_iter("weapon") do
        local value = equip_value(weapon, true, cur_equip, "bless")
        if value > 0 and (not best_value or value > best_value) then
            best_weapon = item
            best_value = value
        end
    end

    if best_weapon then
        use_ability("Brand Weapon With Holy Wrath", item_letter(best_weapon))
        return true
    end

    return false
end

function can_receive_okawaru_weapon()
    return not c_persist.okawaru_weapon_gifted
        and you.god() == "Okawaru"
        and you.piety_rank() >= 6
        and contains_string_in("Receive Weapon", ability_names())
        and can_invoke()
end

function can_receive_okawaru_armour()
    return not c_persist.okawaru_armour_gifted
        and you.god() == "Okawaru"
        and you.piety_rank() >= 6
        and contains_string_in("Receive Armour", ability_names())
        and can_invoke()
end

function can_read_acquirement()
    return find_item("scroll", "acquirement") and can_read()
end

function can_invent_gizmo()
    return not c_persist.invented_gizmo
        and you.xl() >= 14
        and contains_string_in("Invent Gizmo", ability_names())
end

function plan_move_for_acquirement()
    if qw.danger_in_los
            or not qw.position_is_safe
            or not can_read_acquirement()
                and not can_receive_okawaru_weapon()
                and not can_receive_okawaru_armour()
            or not destroys_items_at(const.origin)
            or unable_to_move()
            or dangerous_to_move() then
        return false
    end

    for pos in radius_iter(const.origin, qw.los_radius) do
        local map_pos = position_sum(qw.map_pos, pos)
        if map_is_reachable_at(map_pos) and not destroys_items_at(pos) then
            local result = best_move_towards(map_pos)
            if result and move_to(result.move) then
                return true
            end
        end
    end

    return false
end

function plan_receive_okawaru_weapon()
    if qw.danger_in_los
            or not qw.position_is_safe
            or not can_receive_okawaru_weapon() then
        return false
    end

    if use_ability("Receive Weapon") then
        c_persist.okawaru_weapon_gifted = true
        return true
    end

    return false
end

function plan_receive_okawaru_armour()
    if qw.danger_in_los
            or not qw.position_is_safe
            or not can_receive_okawaru_armour() then
        return false
    end

    if use_ability("Receive Armour") then
        c_persist.okawaru_armour_gifted = true
        return true
    end

    return false
end

function plan_invent_gizmo()
    if qw.danger_in_los
            or not qw.position_is_safe
            or not can_invent_gizmo() then
        return false
    end

    if use_ability("Invent Gizmo") then
        c_persist.invented_gizmo = true
        return true
    end

    return false
end

function plan_maybe_pickup_acquirement()
    if qw.acquirement_pickup then
        magic(",")
        qw.acquirement_pickup = false
        return true
    end

    return false
end

function plan_upgrade_weapon()
    if unable_to_wield_weapon() or you.race() == "Troll" then
        return false
    end

    local best_equip = best_equip_set()
    for weapon in equip_set_slot_iter(best_equip, "weapon") do
        if equip_item(weapon, "weapon", best_equip) then
            return true
        end
    end

    return false
end

function plan_remove_shield()
    if you.race() == "Felid" then
        return false
    end

    local best_equip = best_equip_set()
    for shield in equipped_slot_iter("shield") do
        if not item_in_equip_set(shield, best_equip)
                and unequip_item(shield) then
            return true
        end
    end

    return false
end

function plan_wear_shield()
    if you.race() == "Felid" then
        return false
    end

    local best_equip = best_equip_set()
    for shield in equip_set_slot_iter(best_equip, "shield") do
        if equip_item(shield, "shield", best_equip) then
            return true
        end
    end

    return false
end

function plan_remove_terrible_rings()
    if you.berserk()
            or (you.strength() > 0
                and you.intelligence() > 0
                and you.dexterity() > 0) then
        return false
    end

    local equip = best_equip_set()
    local worst_ring, worst_value = equip_set_value_search(equip,
        function(item)
            return item.equipped
                and equip_slot(item) == "ring"
                and can_swap_item(item, true)
        end, true)
    if not worst_ring or worst_value >= 0 then
        return false
    end

    say("REMOVING " .. worst_ring.name() .. ".")
    magic("R" .. item_letter(worst_ring))
    return true
end

function plan_upgrade_equipment()
    if qw.danger_in_los or not qw.position_is_safe then
        return false
    end

    local best_equip = best_equip_set()
    for slot, item in equip_set_iter(best_equip, const.upgrade_slots) do
        if equip_item(item, slot, best_equip) then
            return true
        end
    end

    return false
end

function plan_remove_equipment()
    if qw.danger_in_los or not qw.position_is_safe then
        return false
    end

    local best_equip = best_equip_set()
    for slot, item in equipped_slots_iter(const.upgrade_slots) do
        if not item_in_equip_set(item, best_equip)
                and unequip_item(item, slot) then
            return true
        end
    end

    return false
end

function plan_unwield_weapon()
    local best_equip = best_equip_set()
    for weapon in equipped_slot_iter("weapon") do
        if not item_in_equip_set(weapon, best_equip)
                and unequip_item(weapon, "weapon") then
            return true
        end
    end

    return false
end

-- Do we want to keep this brand?
function weapon_brand_is_great(weapon)
    local brand = weapon.ego()
    if brand == "speed"
            or brand == "spectralizing"
            or brand == "holy wrath"
                and (undead_or_demon_branch_soon() or future_tso) then
        return true
    -- The best that brand weapon can give us for ranged weapons.
    elseif brand == "heavy" and want_ranged_weapon() then
        return true
    -- The best that brand weapon can give us for melee weapons. No longer as
    -- good once we have the ORB. XXX: Nor if we're only doing undead or demon
    -- branches from now on.
    elseif brand == "vampirism" then
        return not qw.have_orb
    else
        return false
    end
end

function want_cure_mutations()
    return base_mutation("inhibited regeneration") > 0
            and you.race() ~= "Ghoul"
        or base_mutation("teleportitis") > 0
        or base_mutation("inability to drink after injury") > 0
        or base_mutation("inability to read after injury") > 0
        or base_mutation("deformed body") > 0
            and you.race() ~= "Naga"
            and you.race() ~= "Armataur"
            and (armour_plan() == "heavy"
                or armour_plan() == "large")
        or base_mutation("berserk") > 0
        or base_mutation("deterioration") > 1
        or base_mutation("frail") > 0
        or base_mutation("no potion heal") > 0
            and you.race() ~= "Vine Stalker"
        or base_mutation("heat vulnerability") > 0
            and (you.res_fire() < 0
                or you.res_fire() < 3
                    and (branch_soon("Zot") or branch_soon("Geh")))
        or base_mutation("cold vulnerability") > 0
            and (you.res_cold() < 0
                or you.res_cold() < 3 and branch_soon("Coc"))
end

function get_enchantable_weapon(unknown)
    if unknown == nil then
        unknown = true
    end

    local best_equip = best_equip_set()
    local slay_value = linear_property_value("Slay")
    local enchantable_weapon
    for weapon in inventory_slot_iter("weapon") do
        if weapon.is_enchantable then
            local equip = best_inventory_equip(weapon)
            if equip and equip.value > 0
                    and (not best_equip
                        or equip.value + slay_value > best_equip.value) then
                best_equip = equip
            end

            if unknown then
                enchantable_weapon = weapon
            end
        end
    end

    if not best_equip then
        return enchantable_weapon
    end

    -- Because of Coglins, we want to find the best of what may be two
    -- enchantable weapons.
    return equip_set_value_search(best_equip,
        function(item)
            return equip_slot(item) == "weapon" and item.is_enchantable
        end)
end

function get_brandable_weapon(unknown)
    if unknown == nil then
        unknown = true
    end

    local best_equip = best_equip_set()
    if not best_equip or not best_equip.weapon then
        return
    end

    local best_weapon = equip_set_value_search(best_equip,
        function(item)
            return equip_slot(item) == "weapon"
                and not item.artefact
                and not weapon_brand_is_great(item)
        end)
    if not unknown then
        return best_weapon
    end

    best_equip = nil
    local fallback_weapon
    for weapon in inventory_slot_iter("weapon") do
        if not weapon.artefact then
            fallback_weapon = weapon

            local equip = best_inventory_equip(weapon)
            if equip and equip.value > 0
                    and (not best_equip or equip.value > best_equip.value) then
                best_equip = equip
            end
        end
    end
    if best_equip then
        return equip_set_value_search(best_equip,
            function(item)
                return equip_slot(item) == "weapon"
                    and not item.artefact
            end)
    end

    return fallback_weapon
end

function body_armour_is_great_to_enchant(armour)
    local name = armour.name("base")
    local ap = armour_plan()
    if ap == "heavy" then
        return name == "golden dragon scales"
            or name == "crystal plate armour"
            or name == "plate armour" and item_property("rF", armour) > 0
            or name == "pearl dragon scales"
    elseif ap == "large" then
        return name:find("dragon scales")
    elseif ap == "dodgy" then
        return armour.encumbrance <= 11 and name:find("dragon scales")
    else
        return name:find("dragon scales")
            or name == "robe" and item_property("rF", armour) > 0
    end
end

function body_armour_is_good_to_enchant(armour)
    local name = armour.name("base")
    local ap = armour_plan()
    if ap == "heavy" then
        return name == "plate armour" or name:find("dragon scales")
    elseif ap == "large" then
        return false
    elseif ap == "dodgy" then
        return name == "ring mail"
            or name == "robe" and armour.ego() == "resistance"
    else
        return name == "robe" and item_property("rF", armour) > 0
            or name == "troll leather armour"
    end
end

function get_enchantable_armour(scroll_unknown)
    if scroll_unknown == nil then
        scroll_unknown = true
    end

    local best_equip = best_equip_set()
    local ac_value = linear_property_value("AC")
    local fallback_armour, body_armour
    local best_armour = equip_set_value_search(best_equip,
        function(item)
            if item.class(true) ~= "armour" or not item.is_enchantable then
                return false
            end

            local slot = equip_slot(item)
            return slot ~= "shield"
                and (slot ~= "body"
                    or body_armour_is_great_to_enchant(item))
        end)
    if best_armour then
        return best_armour
    end

    local body_armour
    if best_equip.body then
        body_armour = best_equip.body[1]
    end
    if body_armour
            and body_armour.is_enchantable
            and body_armour_is_good_to_enchant(body_armour) then
        return body_armour
    end

    local shield
    if best_equip.shield then
        shield = best_equip.shield[1]
    end
    if shield and shield.is_enchantable then
        return shield
    end

    if not unknown then
        return
    end

    for slot, armour in inventory_slot_iter(const.armour_slots) do
        if armour.is_enchantable then
            return armour
        end
    end
end

function plan_use_good_consumables()
    if qw.danger_in_los then
        return false
    end

    local read_ok = can_read()
    local drink_ok = can_drink()
    for item in inventory_iter() do
        if read_ok and item.class(true) == "scroll" then
            if item.name():find("acquirement")
                    and not destroys_items_at(const.origin) then
                read_scroll(item)
                return true
            elseif item.name():find("enchant weapon")
                    and get_enchantable_weapon(false) then
                read_scroll(item)
                return true
            elseif item.name():find("brand weapon")
                    and get_brandable_weapon(false) then
                read_scroll(item)
                return true
            elseif item.name():find("enchant armour")
                    and get_enchantable_armour(false) then
                read_scroll(item)
                return true
            end
        elseif drink_ok and item.class(true) == "potion" then
            if item.name():find("experience") then
                drink_potion(item)
                return true
            end

            if item.name():find("mutation") and want_cure_mutations() then
                drink_potion(item)
                return true
            end
        end
    end

    return false
end

function want_drop_item(item)
    local class = item.class(true)
    if class == "missile" and not want_missile(item) then
        return true
    end

    -- Since DCSS 0.34, potions, scrolls, and other evokable items are stored
    -- in separate unlimited inventories, so there's no reason to drop them.
    -- (Dropping them by letter is also unreliable, since consumable
    -- inventories use their own separate sets of 52 letters.)
    if class == "potion" or class == "wand" or class == "scroll" then
        return false
    end

    return equip_slot(item)
        and equip_is_dominated(item)
        and (not item.equipped or can_swap_item(item, true))
end

function plan_drop_items()
    if qw.danger_in_los or not qw.position_is_safe then
        return false
    end

    for item in inventory_iter() do
        if want_drop_item(item) then
            say("DROPPING " .. item.name() .. ".")
            magic("d" .. item_letter(item) .. "\r")
            return true
        end
    end

    return false
end

function quaff_unided_potion(min_quantity)
    for it in inventory_iter() do
        if it.class(true) == "potion"
                and (not min_quantity or it.quantity >= min_quantity)
                and not it.is_identified then
            drink_potion(it)
            return true
        end
    end
    return false
end

function plan_quaff_unided_potions()
    if qw.danger_in_los or not qw.position_is_safe or not can_drink() then
        return false
    end

    return quaff_unided_potion(2)
end

function read_unided_scroll()
    for item in inventory_iter() do
        if item.class(true) == "scroll" and not item.is_identified then
            read_scroll(item, ".Y")
            return true
        end
    end

    return false
end

function plan_read_unided_scrolls()
    if qw.danger_in_los or not qw.position_is_safe or not can_read() then
        return false
    end

    return read_unided_scroll()
end

function plan_use_identify_scrolls()
    if qw.danger_in_los or not qw.position_is_safe or not can_read() then
        return false
    end

    local id_scroll = find_item("scroll", "identify")
    if not id_scroll then
        return false
    end

    if not get_unidentified_item() then
        return false
    end

    read_scroll(id_scroll)
    return true
end

function want_to_buy(it)
    local class = it.class(true)
    if class == "missile" then
        return false
    elseif class == "scroll" then
        local sub = it.subtype()
        if sub == "identify" and count_item("scroll", sub) > 9 then
            return false
        end
    end
    return autopickup(it, it.name())
end

function shop_item_sort(i1, i2)
    return crawl.string_compare(i1[1].name(), i2[1].name()) < 0
end

function plan_shop()
    if qw.danger_in_los
            or view.feature_at(0, 0) ~= "enter_shop"
            or free_inventory_slots() == 0 then
        return false
    end
    if you.berserk() or you.caught() or you.mesmerised() then
        return false
    end

    local it, price, on_list
    local sitems = items.shop_inventory()
    table.sort(sitems, shop_item_sort)
    for n, e in ipairs(sitems) do
        it = e[1]
        price = e[2]
        on_list = e[3]

        if want_to_buy(it) then
            -- We want the item. Can we afford buying it now?
            local wealth = you.gold()
            if price <= wealth then
                say("BUYING " .. it.name() .. " (" .. price .. " gold).")
                magic("<//" .. items.index_to_letter(n - 1) .. "\ry")
                return
            -- Should in theory also work in Bazaar, but doesn't make much
            -- sense (since we won't really return or acquire money and travel
            -- back here)
            elseif not on_list
                 and not in_branch("Bazaar") and not branch_soon("Zot") then
                say("SHOPLISTING " .. it.name() .. " (" .. price .. " gold"
                 .. ", have " .. wealth .. ").")
                magic("<//" .. string.upper(items.index_to_letter(n - 1)))
                return
            end
        elseif on_list then
            -- We no longer want the item. Remove it from shopping list.
            magic("<//" .. string.upper(items.index_to_letter(n - 1)))
            return
        end
    end
    return false
end

function plan_shopping_spree()
    if unable_to_travel() or goal_status ~= "Shopping" then
        return false
    end

    which_item = can_afford_any_shoplist_item()
    if not which_item then
        -- Remove everything on shoplist.
        clear_out_shopping_list()
        -- Record that we are done shopping this game.
        c_persist.done_shopping = true
        update_goal()
        return false
    end

    magic("$" .. items.index_to_letter(which_item - 1))
    return true
end

-- Usually, this function should return `1` or `false`.
function can_afford_any_shoplist_item()

    local shoplist = items.shopping_list()

    if not shoplist then
        return false
    end

    local price
    for n, entry in ipairs(shoplist) do
        price = entry[2]
        -- Since the shopping list holds no reference to the item itself,
        -- we cannot check want_to_buy() until arriving at the shop.
        if price <= you.gold() then
            return n
        end
    end
    return false
end

-- Clear out shopping list if no affordable items are left before entering Zot
function clear_out_shopping_list()
    local shoplist = items.shopping_list()
    if not shoplist then
        return
    end

    say("CLEARING SHOPPING LIST")
    -- Press ! twice to toggle action to 'delete'
    local clear_shoplist_magic = "$!!"
    for n, it in ipairs(shoplist) do
        clear_shoplist_magic = clear_shoplist_magic .. "a"
    end
    magic(clear_shoplist_magic)
    qw.do_dummy_action = false
    coroutine.yield()
end

-- These plans will only execute after a successful acquirement.
function set_plan_acquirement()
    plans.acquirement = cascade {
        {plan_maybe_pickup_acquirement, "try_pickup_acquirement"},
        {plan_move_for_acquirement, "move_for_acquirement"},
        {plan_receive_okawaru_weapon, "receive_okawaru_weapon"},
        {plan_receive_okawaru_armour, "receive_okawaru_armour"},
        {plan_invent_gizmo, "invent_gizmo"},
    }
end

function choose_acquirement(acquire_type)
    local acq_items = items.acquirement_items(acquire_type)
    local cur_equip = inventory_equip(const.inventory.equipped)
    for _, item in ipairs(acq_items) do
        local min_val, max_val = equip_value(item)
        say("Offered " .. item.name() .. " with min/max values "
            .. tostring(min_val) .. "/" .. tostring(max_val))
    end

    local index = best_acquirement_index(acq_items)
    if index then
        if acquire_type ~= const.acquire.gizmo then
            qw.acquirement_pickup = true
        end

        say("ACQUIRING " .. acq_items[index].name())
        return index
    else
        say("GAVE UP ACQUIRING")
        return 1
    end
end

function c_choose_acquirement()
    return choose_acquirement(const.acquire.scroll)
end

function c_choose_okawaru_weapon()
    return choose_acquirement(const.acquire.okawaru_weapon)
end

function c_choose_okawaru_armour()
    return choose_acquirement(const.acquire.okawaru_armour)
end

function c_choose_coglin_gizmo()
    return choose_acquirement(const.acquire.gizmo)
end

function get_unidentified_item()
    local id_item
    for item in inventory_iter() do
        if item.class(true) == "potion"
                and not item.is_identified
                -- Prefer identifying potions over scrolls and prefer
                -- identifying smaller stacks.
                and (not id_item
                    or id_item.class(true) ~= "potion"
                    or item.quantity < id_item.quantity) then
            id_item = item
        elseif item.class(true) == "scroll"
                and not item.is_identified
                and (not id_item or id_item.class(true) ~= "potion")
                and (not id_item or item.quantity < id_item.quantity) then
            id_item = item
        end
    end

    return id_item
end

function c_choose_identify()
    local id_item = get_unidentified_item()
    if id_item then
        say("IDENTIFYING " .. id_item.name())
        return item_letter(id_item)
    end
end

function c_choose_brand_weapon()
    local weapon = get_brandable_weapon()
    if weapon then
        say("BRANDING " .. weapon:name() .. ".")
        return item_letter(weapon)
    end
end

function c_choose_enchant_weapon()
    local weapon = get_enchantable_weapon()
    if weapon then
        say("ENCHANTING " .. weapon:name() .. ".")
        return item_letter(weapon)
    end
end

function c_choose_enchant_armour()
    local armour = get_enchantable_armour()
    if armour then
        say("ENCHANTING " .. armour:name() .. ".")
        return item_letter(armour)
    end
end
------------------
-- Plans specific to the Orb run.

function want_to_orbrun_heal_wounds()
    if not qw.have_orb then
        return false
    end

    if qw.danger_in_los then
        return hp_is_low(25) or hp_is_low(50) and you.teleporting()
    else
        return hp_is_low(50)
    end
end

function plan_go_to_orb()
    if unable_to_travel()
            or goal_status ~= "Orb"
            or not c_persist.found_orb then
        return false
    end

    magicfind("orb of zot")
    return true
end
------------------
-- Plans specific to Pandemonium.

function want_to_be_in_pan()
    return goal_branch == "Pan" and not have_branch_runes("Pan")
end

function plan_go_to_pan_portal()
    if unable_to_travel()
            or in_branch("Pan")
            or not want_to_be_in_pan()
            or not branch_found("Pan") then
        return false
    end

    magicfind("halls of Pandemonium")
    return true
end

function plan_go_to_pan_downstairs()
    if not unable_to_travel() and in_branch("Pan") then
        magic("X>\r")
        return true
    end

    return false
end

local pan_failed_rune_count = -1
function want_to_dive_pan()
    return in_branch("Pan")
        and you.num_runes() > pan_failed_rune_count
        and (you.have_rune("demonic") and not have_branch_runes("Pan")
            or dislike_pan_level)
end

function plan_dive_go_to_pan_downstairs()
    if want_to_dive_pan() then
        magic("X>\r")
        return true
    end
    return false
end

function plan_go_to_pan_exit()
    if not unable_to_travel()
            and in_branch("Pan")
            and not want_to_be_in_pan() then
        magic("X<\r")
        return true
    end

    return false
end

function plan_enter_pan()
    if view.feature_at(0, 0) == branch_entrance("Pan")
            and want_to_be_in_pan()
            and not unable_to_use_stairs() then
        go_downstairs(true)
        return true
    end

    return false
end

local pan_stairs_turn = -100
function plan_go_down_pan()
    if view.feature_at(0, 0) ~= "transit_pandemonium"
                and view.feature_at(0, 0) ~= branch_exit("Pan")
            or unable_to_use_stairs() then
        return false
    end

    if pan_stairs_turn == you.turns() then
        magic("X" .. control('f'))
        return true
    end

    pan_stairs_turn = you.turns()
    go_downstairs(true)
    -- In case we are trying to leave a rune level.
    return nil
end

function plan_dive_pan()
    if not want_to_dive_pan() or unable_to_use_stairs() then
        return false
    end

    if view.feature_at(0, 0) == "transit_pandemonium"
            or view.feature_at(0, 0) == branch_exit("Pan") then
        if pan_stairs_turn == you.turns() then
            pan_failed_rune_count = you.num_runes()
            return false
        end

        pan_stairs_turn = you.turns()
        dislike_pan_level = false
        go_downstairs(true)
        -- In case we are trying to leave a rune level.
        return
    end

    return false
end

function plan_exit_pan()
    if view.feature_at(0, 0) == branch_exit("Pan")
            and not want_to_be_in_pan()
            and not unable_to_use_stairs() then
        go_upstairs()
        return true
    end

    return false
end
------------------
-- General plans related to religion

function plan_go_to_altar()
    local god = goal_god(goal_status)
    if unable_to_travel() or not god then
        return false
    end

    magicfind("altar&&<<of " .. god .. ">>")
    return true
end

function plan_abandon_god()
    if goal_god(goal_status) == "No God"
            or you.class() == "Chaos Knight"
                and you.god() == "Xom"
                and qw.ck_abandon_xom then
        magic("aXYY")
        return true
    end

    return false
end

function plan_join_beogh()
    if you.race() ~= "Hill Orc"
            or goal_status ~= "God:Beogh"
            or you.confused()
            or you.silenced() then
        return false
    end

    if use_ability("Convert to Beogh", "YY") then
        return true
    end

    return false
end

function plan_use_altar()
    local god = goal_god(goal_status)
    if not god
            or view.feature_at(0, 0) ~= god_altar(god)
            or not can_use_altars() then
        return false
    end

    magic("<JY")
    return true
end

function plan_sacrifice()
    if you.god() ~= "Ru" or not can_invoke() then
        return false
    end

    -- Sacrifices that we won't do for now: words, drink, courage, durability,
    -- hand, resistance, purity, health.
    good_sacrifices = {
        "Sacrifice Artifice",   -- 55
        "Sacrifice Love",       -- 40
        "Sacrifice Experience", -- 40
        "Sacrifice Nimbleness", -- 30
        "Sacrifice Skill",      -- 30
        "Sacrifice Arcana",     -- 25
        "Sacrifice an Eye",     -- 20
        "Sacrifice Stealth",    -- 15
        "Sacrifice Essence",    -- variable
        "Reject Sacrifices",
    }
    for _, sacrifice in ipairs(good_sacrifices) do
        if use_ability(sacrifice, "YY") then
            return true
        end
    end
    return false
end

local did_ancestor_identity = false
function plan_ancestor_identity()
    if you.god() ~= "Hepliaklqana" or not can_invoke() then
        return false
    end

    if not did_ancestor_identity then
        use_ability("Ancestor Identity",
            "\b\b\b\b\b\b\b\b\b\b\b\b\b\b\belliptic\ra")
        did_ancestor_identity = true
        return true
    end
    return false
end

function plan_ancestor_life()
    if you.god() ~= "Hepliaklqana" or not can_invoke() then
        return false
    end

    local ancestor_options = {"Knight", "Battlemage", "Hexer"}
    if use_ability("Ancestor Life: " ..
            ancestor_options[crawl.roll_dice(1, 3)], "Y") then
        return true
    end

    return false
end
------------------
-- The rest plan cascade.

function plan_cure_poison()
    if not you.poisoned() or you.poison_survival() > 1 then
        return false
    end

    if drink_by_name("curing") then
        say("(to cure poison)")
        return true
    end

    if can_trogs_hand() then
        trogs_hand()
        return true
    end

    if can_purification() then
        use_purification()
        return true
    end

    return false
end

function should_rest()
    if qw.danger_in_los and not qw.all_enemies_safe or qw.position_is_cloudy then
        return false
    end

    if qw.have_orb then
        return you.confused()
            or transformed()
            or you.slowed() and not qw.slow_aura
            or you.berserk()
            or you.teleporting()
            or you.status("spiked")
    end

    if want_to_move_to_abyss_objective() then
        return false
    end

    return you.berserk()
        or you.turns() < hiding_turn_count + 10
        or you.god() == "Makhleb"
            and you.turns() <= hostile_servants_timer + 100
        or reason_to_rest(99.9)
end

-- Check statuses to see whether there is something to rest off, does not
-- include some things in should_rest() because they are not clearly good to
-- wait out with monsters around.
function reason_to_rest(percentage)
    if qw.starting_spell or god_uses_mp() then
        local mp, mmp = you.mp()
        if mp < mmp then
            return true
        end
    end

    if you.race() ~= "Djinni"
            and you.god() == "Elyvilon"
            and you.piety_rank() >= 4 then
        local mp, mmp = you.mp()
        if mp < mmp and mp < 10 then
            return true
        end
    end

    return you.confused()
        or transformed()
        or you.slowed() and not qw.slow_aura
        or you.exhausted()
        or you.teleporting()
            and not teleporting_before_dangerous_stairs()
        or you.status("on berserk cooldown")
        or you.status("marked")
        or you.status("spiked")
        or you.status("weak-willed") and not in_branch("Tar")
        or you.status("fragile (+50% incoming damage)")
        or you.status("attractive")
        or you.status("frozen")
        or you.silencing()
        or you.corrosion() > qw.base_corrosion
        or hp_is_low(percentage)
            -- Don't rest if we're in good shape and have divine warriors nearby.
            and not (you.god() == "the Shining One"
                and check_divine_warriors(2)
                and not hp_is_low(75))
end

function should_ally_rest()
    if qw.danger_in_los
            or you.god() ~= "Yredelemnul" and you.god() ~= "Beogh" then
        return false
    end

    for pos in square_iter(const.origin, 3) do
        local mons = get_monster_at(pos)
        if mons and mons:is_friendly() and mons:damage_level() > 0 then
            return true
        end
    end

    return false
end

function wait_one_turn(short_delay)
    magic("s")
    if short_delay then
        next_delay = 5
    end
end

function long_rest()
    magic("5")
end

function plan_long_rest()
    if should_rest() then
        long_rest()
        return true
    end

    return false
end

function plan_rest_one_turn()
    if should_rest() then
        wait_one_turn(true)
        return true
    end

    return false
end

function set_plan_rest()
    plans.rest = cascade {
        {plan_cure_poison, "cure_poison"},
        {plan_long_rest, "try_long_rest"},
        {plan_rest_one_turn, "rest_one_turn"},
    }
end
function get_starting_spell()
    if you.xl() > 4 or you.god() == "Trog" then
        return
    end

    local spell_list = { "Foxfire", "Freeze", "Magic Dart", "Soul Splinter", "Sandblast",
        "Shock", "Sting", "Summon Small Mammal" }
    for _, sp in ipairs(spell_list) do
        if spells.memorised(sp) and spells.fail(sp) <= 25 then
            return sp
        end
    end
end

function spell_range(sp)
    if sp == "Summon Small Mammal" then
        return qw.los_radius
    elseif sp == "Beastly Appendage" then
        return 4
    elseif sp == "Sandblast" then
        return 4
    else
        return spells.range(sp)
    end
end

function spell_castable(sp)
    if you.silenced()
            or you.confused()
            or you.berserk()
            or in_bad_form()
            or can_use_mp(spells.mana_cost(sp)) then
        return false
    end

    if sp == "Beastly Appendage" then
        return transformed()
    elseif sp == "Summon Small Mammal" then
        local count = 0
        for pos in square_iter(const.origin) do
            local mons = get_monster_at(pos)
            if mons and mons:is_friendly() then
                count = count + 1
            end
        end
        if count >= 2 then
            return false
        end
    end

    return true
end

function distance_to_tabbable_enemy()
    local best_dist = 10
    for _, enemy in ipairs(qw.enemy_list) do
        if enemy:distance() < best_dist
                and (enemy:player_has_path_to_melee()
                    or enemy:player_can_wait_for_melee()) then
            best_dist = enemy:distance()
        end
    end
    return best_dist
end

function plan_starting_spell()
    if not qw.starting_spell or not spell_castable(qw.starting_spell) then
        return false
    end

    local dist = distance_to_tabbable_enemy()
    if dist < 2 and weapons_match_skill(weapon_skill()) then
        return false
    end

    if dist > spell_range(qw.starting_spell) then
        return false
    end

    say("CASTING " .. qw.starting_spell)
    if spells.range(qw.starting_spell) > 0 then
        magic("z" .. spells.letter(qw.starting_spell) .. "f")
    else
        magic("z" .. spells.letter(qw.starting_spell))
    end
    return true
end
----------------------
-- Stair-related plans

function go_upstairs(confirm)
    magic("<" .. (confirm and "Y" or ""))
end

function go_downstairs(confirm)
    magic(">" .. (confirm and "Y" or ""))
end

function plan_go_to_unexplored_stairs()
    if unable_to_travel()
            or goal_travel.want_go
            or not goal_travel.stairs_dir then
        return false
    end

    if map_mode_search_attempts == 1 then
        map_mode_search_attempts = 0
        disable_autoexplore = false
        return false
    end

    local key = dir_key(goal_travel.stairs_dir)
    local hash = hash_position(qw.map_pos)
    local searches = map_mode_searches[key]
    local count = 1
    while searches and searches[hash] and searches[hash][count] do
        -- Trying to go one past this count lands us at the same destination as
        -- the count, so there are no more accessible unexplored stairs to be
        -- found from where we are, and we stop the search. The backtrack plan
        -- can take over from here.
        if searches[hash][count] == searches[hash][count + 1] then
            return false
        end

        count = count + 1
    end

    map_mode_search_key = key
    map_mode_search_hash = hash
    map_mode_search_count = count
    map_mode_search_attempts = 1
    magic("X" .. key:rep(count) .. "\r")
end

function plan_go_to_transporter()
    if unable_to_travel()
            or not want_to_use_transporters()
            or transp_search then
        return false
    end

    local search_count
    if in_branch("Gauntlet") then
        -- Maps can have functionally different types of transporter routes and
        -- always start the player closest to a route of one type, so randomize
        -- which of the starting transporters we choose. No Gauntlet map has
        -- more than 3 starting transporters, and most have two, so use '>' 1
        -- to 4 times to reduce bias.
        if transp_zone == 0 then
            search_count = crawl.roll_dice(1, 4)
        -- After the first transporter, always take the closest one. This is
        -- important for gammafunk_gauntlet_77_escape_option so we don't take
        -- the early exit after each portal.
        else
            search_count = 1
        end
    else
        search_count = 1
        while transp_map[transp_zone]
                and transp_map[transp_zone][search_count] do
            search_count = search_count + 1
        end
    end

    transp_search_zone = transp_zone
    transp_search_count = search_count
    magic("X" .. (">"):rep(search_count) .. "\r")
    return true
end

function plan_transporter_orient_exit()
    if unable_to_move() or not transp_orient then
        return false
    end

    magic("X<\r")
    return true
end

function unable_to_use_transporters()
    return unable_to_move() or you.mesmerised()
end

function plan_enter_transporter()
    if not transp_search
            or view.feature_at(0, 0) ~= "transporter"
            or unable_to_use_transporters() then
        return false
    end

    magic(">")
    return true
end

function plan_take_unexplored_stairs()
    if not goal_travel.stairs_dir or unable_to_use_stairs() then
        return false
    end

    local feat = view.feature_at(0, 0)
    local dir, num = stone_stairs_type(feat)
    if not dir or dir ~= goal_travel.stairs_dir then
        return false
    end

    local state = get_stone_stairs(where_branch, where_depth, dir, num)
    if state.feat >= const.explore.explored then
        return false
    end

    -- Ensure that we autoexplore any new area we arrive in, otherwise, if we
    -- have completed autoexplore at least once, we may immediately leave once
    -- we see we've found the last missing staircase.
    reset_autoexplore(make_level(where_branch, where_depth + dir))

    if dir == const.dir.up then
        go_upstairs()
    else
        go_downstairs()
    end
    return true
end

-- Backtrack to the previous level if we're trying to explore stairs on a
-- destination level yet have no further accessible unexplored stairs. We
-- require a travel stairs search direction to know whether to attempt this and
-- what direction we should backtrack. Stairs are reset in the relevant
-- directions on both levels so after we explore the pair of stairs used to
-- return to the previous level, we'll take a different set of stairs from that
-- level via a new travel stairs search direction.
function plan_unexplored_stairs_backtrack()
    if unable_to_travel() or goal_travel.want_go or not goal_travel.stairs_dir then
        return false
    end

    local next_depth = where_depth + goal_travel.stairs_dir
    reset_stone_stairs(where_branch, where_depth, goal_travel.stairs_dir)
    reset_stone_stairs(where_branch, next_depth, -goal_travel.stairs_dir)
    send_travel(where_branch, next_depth)
    return true
end

function plan_go_to_upstairs()
    magic("X<\r")
    return true
end

function unable_to_use_stairs()
    return unable_to_move() or you.mesmerised()
end

function count_stair_followers(radius)
    return count_enemies(radius,
        function (mons)
            return mons:can_seek() and mons:can_use_stairs()
        end)
end

function want_to_stairdance_up()
    -- Assume we'd rather follow through with our teleport rather than take
    -- stairs.
    if you.teleporting() then
        return false
    end

    local feat = view.feature_at(0, 0)
    if not qw.can_flee_upstairs or not feature_is_upstairs(feat) then
        return false
    end

    if in_bad_form() then
        return true
    end

    local state = get_destination_stairs(where_branch, where_depth, feat)
    if state and not state.safe then
        return false
    end

    local n = stairdance_count[where] or 0
    if n >= 20 then
        return false
    end

    if you.caught()
            or you.constricted()
            or check_brothers_in_arms(3)
            or check_greater_servants(3)
            or check_divine_warriors(3) then
        return false
    end

    local only_when_safe = you.berserk() or hp_is_low(33)
    local follow_count = count_stair_followers(1)
    local other_count = #qw.enemy_list - follow_count
    if only_when_safe and follow_count > 0 then
        return false
    end

    -- We have no stair followers, so we're going up because we're either
    -- fleeing or we want to rest safely.
    if follow_count == 0 and want_to_flee()
            -- We have stair followers, but there are even more non-following
            -- monsters around, so we go up to fight the following monsters in
            -- probable safety.
            or other_count > 0 and follow_count > 0 then
        stairdance_count[where] = n + 1
        return true
    end

    return false
end

function plan_stairdance_up()
    if unable_to_use_stairs()
            or dangerous_to_move(true)
            or not want_to_stairdance_up() then
        return false
    end

    say("STAIRDANCE")
    go_upstairs(you.status("spiked"))
    return true
end

function want_to_use_escape_hatches(dir)
    return dir == const.dir.up
        and goal_status == "Escape"
        and not branch_is_temporary(where_branch)
        and not in_branch("Tomb")
        and where_depth > 1
        -- It's dangerous to hatch through unexplored areas in Zot as opposed
        -- to simply taking an explored route through stone stairs. So we only
        -- take a hatch up in Zot if the destination level is fully explored.
        and (where_branch ~= "Zot"
            or explored_level(where_branch, where_depth - 1))
end

function plan_take_escape_hatch()
    local dir = escape_hatch_type(view.feature_at(0, 0))
    if not dir
            or not want_to_use_escape_hatches(dir)
            or unable_to_use_stairs() then
        return false
    end

    if dir == const.dir.up then
        go_upstairs()
    else
        go_downstairs()
    end

    return true
end

function plan_move_towards_escape_hatch()
    if not want_to_use_escape_hatches(const.dir.up)
            or unable_to_move()
            or dangerous_to_move() then
        return false
    end

    local result = best_move_towards_positions(qw.flee_positions, true)
    if not result then
        return false
    end

    -- The best flee position is not a hatch.
    if not c_persist.up_hatches[hash_position(result.dest)] then
        return false
    end

    return move_to(result.move)
end

function teleporting_before_dangerous_stairs()
    if goal_travel.want_go or not goal_travel.safe_stairs then
        return false
    end

    local feat = view.feature_at(0, 0)
    if feat ~= goal_travel.safe_stairs then
        return false
    end

    local state = get_destination_stairs(where_branch, where_depth, feat)
    local threat = 0
    if state then
        threat = state.threat
    elseif where_branch == "Vaults"
            and where_depth == branch_depth("Vaults") - 1 then
        threat = 25
    end
    return threat >= extreme_threat_level()
end

function plan_teleport_dangerous_stairs()
    if not can_teleport() or not teleporting_before_dangerous_stairs() then
        return false
    end

    return teleport()
end

function plan_use_travel_stairs()
    if unable_to_use_stairs() or dangerous_to_move() then
        return false
    end

    local feat = view.feature_at(0, 0)
    if goal_travel.safe_hatch and not goal_travel.want_go then
        local map_pos = unhash_position(goal_travel.safe_hatch)
        if not positions_equal(qw.map_pos, map_pos)
                or feat ~= "escape_hatch_down" then
            return false
        end
    else
        local feats = goal_travel_features()
        if not feats then
            return false
        end

        if not util.contains(feats, feat) then
            return false
        end
    end

    if feature_uses_map_key(">", feat) then
        go_downstairs()
        return true
    elseif feature_uses_map_key("<", feat) then
        go_upstairs()
        return true
    end

    return false
end

function plan_abort_safe_stairs()
    if goal_travel.want_go or not (goal_travel.safe_stairs or goal_travel.safe_hatch) then
        return false
    end

    -- We need to update goal travel ourself immediately because we also need
    -- to restart the cascade so that previous plans can do something besides
    -- attempting to use safe stairs.
    qw.safe_stairs_failed = true
    update_goal()

    qw.restart_cascade = true
    return true
end
------------------
-- Plans to try when qw is stuck with no viable plan to execute.

function plan_random_step()
    if unable_to_move() or dangerous_to_move() then
        return false
    end

    qw.stuck_turns = qw.stuck_turns + 1
    return random_step("stuck")
end

function plan_stuck_initial()
    if qw.stuck_turns <= 50 then
        return plan_random_step()
    end

    return false
end

function plan_stuck_take_escape_hatch()
    local dir = escape_hatch_type(view.feature_at(0, 0))
    if not dir or unable_to_use_stairs() then
        return false
    end

    if dir == const.dir.up then
        go_upstairs()
    else
        go_downstairs()
    end

    return true
end

function plan_stuck_move_towards_escape_hatch()
    if want_to_use_escape_hatches(const.dir.up) then
        return false
    end

    local hatch_dir
    if goal_travel.first_dir then
        hatch_dir = goal_travel.first_dir
    else
        hatch_dir = const.dir.up
    end
    local feat = const.escape_hatches[hatch_dir]

    local result = best_move_towards_features({ feat }, true)
    if result then
        return move_towards_destination(result.move, result.dest, "hatch")
    end

    feat = const.escape_hatches[-hatch_dir]
    result = best_move_towards_features({ feat }, true)
    if result then
        return move_towards_destination(result.move, result.dest, "hatch")
    end

    return false
end

function plan_clear_exclusions()
    local n = clear_exclusion_count[where] or 0
    if n > 20 then
        return false
    end

    clear_exclusion_count[where] = n + 1
    remove_exclusions(true)
    magic("X" .. control('e'))
    qw.do_dummy_action = false
    return true
end

function plan_stuck_dig_grate()
    local wand = find_item("wand", "digging")
    if not wand or not can_evoke() then
        return false
    end

    local grate_offset = 20
    local grate_pos
    for pos in square_iter(const.origin) do
        if view.feature_at(pos.x, pos.y) == "iron_grate" then
            if abs(pos.x) + abs(pos.y) < grate_offset
                    and you.see_cell_solid_see(pos.x, pos.y) then
                grate_pos = pos
                grate_offset = abs(pos.x) + abs(pos.y)
            end
        end
    end

    if grate_offset < 20 then
        return evoke_targeted_item(wand, grate_pos)
    end

    return false
end

function plan_forget_map()
    if not qw.position_is_cloudy
            and not qw.danger_in_los
            and (at_branch_end("Slime") and not have_branch_runes("Slime")
                or at_branch_end("Geh") and not have_branch_runes("Geh")) then
        magic("X" .. control('f'))
        return true
    end

    return false
end

function plan_stuck_teleport()
    if can_teleport() then
        return teleport()
    end

    return false
end

function set_plan_stuck()
    plans.stuck = cascade {
        {plan_abyss_wait_one_turn, "abyss_wait_one_turn"},
        {plan_stuck_take_escape_hatch, "stuck_take_escape_hatch"},
        {plan_stuck_move_towards_escape_hatch, "stuck_move_towards_escape_hatch"},
        {plan_clear_exclusions, "try_clear_exclusions"},
        {plan_stuck_dig_grate, "try_stuck_dig_grate"},
        {plan_forget_map, "try_forget_map"},
        {plan_stuck_initial, "stuck_initial"},
        {plan_stuck_teleport, "stuck_teleport"},
        {plan_random_step, "random_step"},
    }
end
------------------
-- Plans related to the Ziggurat portal.

function plan_zig_fog()
    if not in_branch("Zig")
            or you.berserk()
            or you.teleporting()
            or you.confused()
            or not qw.danger_in_los
            or not hp_is_low(70)
            or count_enemies(qw.los_radius) - count_enemies(2) < 15
            or view.cloud_at(0, 0) ~= nil then
        return false
    end
    return read_scroll_by_name("fog")
end

function plan_move_to_zigfig_location()
    if unable_to_travel()
            or goal_branch ~= "Zig"
            or branch_is_temporary(where_branch)
            or not find_item("misc", "figurine of a ziggurat")
            or not feature_is_critical(view.feature_at(0, 0)) then
        return false
    end

    for pos in adjacent_iter(const.origin) do
        if is_traversable_at(pos)
                and not is_solid_at(pos)
                and not monster_in_way_at(pos, const.origin)
                and is_safe_at(pos)
                and not feature_is_critical(view.feature_at(pos.x, pos.y)) then
            return move_to(pos)
        end
    end

    return false
end

function plan_use_zigfig()
    if goal_branch ~= "Zig"
            or branch_is_temporary(where_branch)
            or qw.danger_in_los
            or not qw.position_is_safe
            or you.berserk()
            or you.confused()
            or feature_is_critical(view.feature_at(0, 0)) then
        return false
    end

    local figurine = find_item("misc", "figurine of a ziggurat")
    if figurine then
        say("MAKING ZIG")
        magic("V" .. item_letter(figurine))
        return true
    end

    return false
end

function plan_go_to_zig_dig()
    if unable_to_travel()
            or goal_branch ~= "Zig"
            or not branch_found("Zig")
            or view.feature_at(0, 0) == branch_entrance("Zig")
            or view.feature_at(3, 1) == branch_entrance("Zig")
            or count_charges("digging") == 0 then
        return false
    end

    magic(control('f') .. portal_entrance_description("Zig") .. "\rayby\r")
    return true
end

function plan_zig_dig()
    local wand = find_item("wand", "digging")
    if not in_branch("Depths")
            or goal_branch ~= "Zig"
            or view.feature_at(3, 1) ~= branch_entrance("Zig")
            or not wand
            or not can_evoke() then
        return false
    end

    return evoke_targeted_item(wand, { x = 1, y = 0 })
end

function plan_zig_go_to_stairs()
    if unable_to_travel() or not in_branch("Zig") then
        return false
    end

    if c_persist.zig_completed then
        magic("X<\r")
    else
        magic("X>\r")
    end
    return true
end

function plan_zig_leave_level()
    if not in_branch("Zig") or unable_to_use_stairs() then
        return false
    end

    if c_persist.zig_completed
            and view.feature_at(0, 0) == branch_exit("Zig") then
        local parent, depth = parent_branch(where_branch)
        remove_portal(make_level(parent, depth), where_branch, true)
        go_upstairs(true)
        return true
    elseif feature_is_downstairs(view.feature_at(0, 0)) then
        go_downstairs()
        return true
    end

    return false
end
------------------
-- The common plan functions and the overall turn plan.

function use_ability(name, extra, mute)
    for letter, abil in pairs(ability_table()) do
        if abil == name then
            -- Want to make sure we don't get a skill selection screen if we
            -- were training Dodging.
            if name == "Sacrifice Nimbleness" then
                you.train_skill("Fighting", 1)
            end

            if not mute then
                say("INVOKING " .. name .. ".")
            end

            magic("a" .. letter .. (extra or ""))
            return true
        end
    end

    return false
end

-- This plan is called outside of the turn plan cascade.
function plan_message()
    if qw.read_message then
        crawl.setopt("clear_messages = false")
        magic("_")
        qw.read_message = false
    else
        crawl.setopt("clear_messages = true")
        magic(":qwqwqw\r")
        qw.read_message = true
        qw.have_message = false
        crawl.delay(2500)
    end
end

function plan_save()
    if goal_status == "Save" then
        c_persist.last_completed_goal = goal_status
        magic(control("s"))
        return true
    end

    return false
end

function plan_quit()
    if goal_status == "Quit" then
        c_persist.last_completed_goal = goal_status
        magic(control('q') .. "yes\r")
        return true
    end

    return false
end

-----------------------------------------
-- Every plan function that might take an action should return as follows:
--   true if tried to do something.
--   false if didn't do anything.
--   nil if should be rerun. This can be used when a plan might fail to consume
--   a turn, allowing the plan to attempt a fallback actions. Plans returning
--   nil must track their function calls carefully with an appropriate
--   variable, otherwise they'll create an infinite loop.

-- This is the bot's flowchart for using plan functions.
function cascade(plans)
    local plan_turns = {}
    local plan_result = {}
    return function ()
        for i, plandata in ipairs(plans) do
            local plan = plandata[1]
            if plan == nil then
                error("No plan function for " .. plandata[2])
            end

            if qw.restart_cascade
                    or you.turns() ~= plan_turns[plan]
                    or plan_result[plan] == nil then
                local result = plan()
                if not qw.automatic then
                    return true
                end

                plan_turns[plan] = you.turns()
                plan_result[plan] = result

                if debug_channel("plans") and result ~= false
                        or debug_channel("plans-all") then
                    dsay("Ran " .. plandata[2] .. ": " .. tostring(result))
                end

                if result == nil or result == true then
                    if qw.delayed and result == true then
                        crawl.delay(next_delay)
                    end
                    next_delay = qw.delay_time

                    return
                end
            elseif plan_turns[plan] and plan_result[plan] == true then
                if not plandata[2]:find("^try") then
                    panic(plandata[2] .. " failed despite returning true.")
                end

                local fail_count = c_persist.plan_fail_count[plandata[2]]
                if not fail_count then
                    fail_count = 0
                end
                fail_count = fail_count + 1
                c_persist.plan_fail_count[plandata[2]] = fail_count

                if qw.want_goal_update then
                    update_goal()
                end
            end
        end

        return false
    end
end

function initialize_plan_cascades()
    set_plan_emergency()
    set_plan_attack()
    set_plan_rest()
    set_plan_acquirement()
    set_plan_pre_explore()
    set_plan_pre_explore2()
    set_plan_explore()
    set_plan_explore2()
    set_plan_stuck()
    set_plan_turn()
end

-- This is the main turn planning cascade.
function set_plan_turn()
    plans.turn = cascade {
        {plan_save, "save"},
        {plan_quit, "quit"},
        {plan_ancestor_identity, "try_ancestor_identity"},
        {plan_join_beogh, "join_beogh"},
        {plan_shop, "shop"},
        {plans.emergency, "emergency"},
        {plans.attack, "attack"},
        {plans.rest, "rest"},
        {plans.pre_explore, "pre_explore"},
        {plans.explore, "explore"},
        {plans.pre_explore2, "pre_explore2"},
        {plans.explore2, "explore2"},
        {plans.stuck, "stuck"},
    }
end
-----------------------------------------
-- Player functions and data

const.duration = {
    -- Ignore this duration.
    "ignore",
    -- Ignore this duration if it's a buff.
    "ignore_buffs",
    -- We can get this duration, but it's not currently active.
    "usable",
    -- The duration is currently active.
    "active",
    -- We can get this duration or it's currently active.
    "available",
}

function initialize_player_durations()
    const.player_durations = {
        ["heroism"] = { status = "heroic", can_use_func = can_heroism },
        ["finesse"] = { status = "finesse-ful", can_use_func = can_finesse },
        ["berserk"] = { check_func = you.berserk, can_use_func = can_berserk },
        ["haste"] = { check_func = you.hasted, can_use_func = can_haste },
        ["slow"] = { check_func = you.slowed },
        ["might"] = { check_func = you.mighty, can_use_func = can_might },
        ["weak"] = { status = "weakened" },
    }
end

function can_use_buff(name)
    buff = const.player_durations[name]
    return buff and buff.can_use_func and buff.can_use_func()
end

function duration_active(name)
    duration = const.player_durations[name]
    if not duration then
        return false
    end

    if duration.status then
        return you.status(duration.status)
    else
        return duration.check_func()
    end
end

function have_duration(name, level)
    if level == const.duration.ignore
            or level == const.duration.ignore_buffs
                and const.player_durations[name].can_use_func then
        return false
    elseif level == const.duration.usable then
        return can_use_buff(name)
    elseif level == const.duration.active then
        return duration_active(name)
    else
        return can_use_buff(name) or duration_active(name)
    end
end

function intrinsic_rpois()
    local sp = you.race()
    return sp == "Gargoyle" or sp == "Naga" or sp == "Ghoul" or sp == "Mummy"
end

function intrinsic_relec()
    return sp == "Gargoyle"
end

function intrinsic_sinv()
    local sp = you.race()
    if sp == "Naga"
            or sp == "Felid"
            or sp == "Formicid"
            or sp == "Vampire" then
        return true
    end

    -- We assume that we won't change gods away from TSO.
    if you.god() == "the Shining One" and you.piety_rank() >= 2 then
        return true
    end

    return false
end

function intrinsic_flight()
    local sp = you.race()
    return (sp == "Gargoyle"
        or sp == "Black Draconian") and you.xl() >= 14
        or sp == "Tengu" and you.xl() >= 5
end

function intrinsic_amphibious()
    local sp = you.race()
    return sp == "Merfolk" or sp == "Octopode" or sp == "Barachi"
end

function intrinsic_fumble()
    if intrinsic_amphibious() or intrinsic_flight() then
        return false
    end

    local sp = you.race()
    return not (sp == "Grey Draconian"
        or sp == "Armataur"
        or sp == "Naga"
        or sp == "Troll"
        or sp == "Oni")
end

function intrinsic_evil()
    local sp = you.race()
    return sp == "Demonspawn"
        or sp == "Mummy"
        or sp == "Ghoul"
        or sp == "Vampire"
end

function intrinsic_undead()
    return you.race() == "Ghoul" or you.race() == "Mummy"
end

-- Returns the player's intrinsic level of an artprop string.
function intrinsic_property(prop)
    if prop == "rF" then
        return you.mutation("fire resistance")
    elseif prop == "rC" then
        return you.mutation("cold resistance")
    elseif prop == "rElec" then
        return you.mutation("electricity resistance")
    elseif prop == "rPois" then
        if intrinsic_rpois() or you.mutation("poison resistance") > 0 then
            return 1
        else
            return 0
        end
    elseif prop == "rN" then
        local val = you.mutation("negative energy resistance")
        if you.god() == "the Shining One" then
            val = val + math.floor(you.piety_rank() / 3)
        end
        return val
    elseif prop == "Will" then
        return you.mutation("strong-willed") + (you.god() == "Trog" and 1 or 0)
    elseif prop == "rCorr" then
        return 0
    elseif prop == "SInv" then
        if intrinsic_sinv() or you.mutation("see invisible") > 0 then
            return 1
        else
            return 0
        end
    elseif prop == "Fly" then
        return intrinsic_flight() and 1 or 0
    elseif prop == "Spirit" then
        return you.race() == "Vine Stalker" and 1 or 0
    end

    return 0
end

--[[
Returns the current level of player property by artprop string. If an item is
provided, assume the item is equipped and try to pretend that it is unequipped.
Does not include some temporary effects.
]]--
function player_property(prop, ignore_equip)
    local value
    local prop_is_stat = false
    if prop == "Str" then
        value = you.strength()
        prop_is_stat = true
    elseif prop == "Dex" then
        value = you.dexterity()
        prop_is_stat = true
    elseif prop == "Int" then
        value = you.intelligence()
        prop_is_stat = true
    else
        value = intrinsic_property(prop)
    end

    for slot, item in equipped_slots_iter() do
        local is_ignored = item_in_equip_set(item, ignore_equip)
        -- For stats, we must remove the value contributed by an ignored
        -- item.
        if is_ignored and prop_is_stat then
            value = value - item_property(prop, item)
        elseif not is_ignored and not prop_is_stat then
            value = value + item_property(prop, item)
        end
    end

    local max_level = const.property_max_levels[prop]
    if max_level and value > max_level then
        value = max_level
    end

    return value
end

function player_resist_percentage(resist, level)
    if level < 0 then
        return 1.5
    elseif level == 0 then
        return 1
    end

    if resist == "rF" or resist == "rC" then
        return level == 1 and 0.5 or (level == 2 and 1 / 3 or 0.2)
    elseif resist == "rElec" then
        return 2 / 3
    elseif resist == "rPois" then
        return 1 / 3
    elseif resist == "rCorr" then
        return 0.5
    elseif resist == "rN" then
        return level == 1 and 0.5 or (level == 2 and 0.25 or 0)
    end
end

-- We group all species into four categories:
-- heavy: species that can use arbitrary armour and aren't particularly great
--        at dodging
-- dodgy: species that can use arbitrary armour but are very good at dodging
-- large: species with armour restrictions that want heavy dragon scales
-- light: species with no body armour or who don't want anything heavier than
--        7 encumbrance
function armour_plan()
    local sp = you.race()
    if sp == "Oni" or sp == "Troll" then
        return "large"
    elseif sp == "Deep Elf" or sp == "Kobold" or sp == "Merfolk" then
        return "dodgy"
    elseif weapon_skill() == "Ranged Weapons"
            or sp:find("Draconian")
            or sp == "Felid"
            or sp == "Octopode"
            or sp == "Spriggan" then
        return "light"
    else
        return "heavy"
    end
end

function expected_armour_multiplier()
    local ap = armour_plan()
    if ap == "heavy" then
        return 2
    elseif ap == "large" or ap == "dodgy" then
        return 1.5
    else
        return 1.25
    end
end

function unfitting_armour()
    local sp = you.race()
    return armour_plan() == "large" or sp == "Armataur" or sp == "Naga"
end

-- Used for backgrounds who don't get to choose a weapon.
function weapon_skill_choice()
    local sp = you.race()
    if sp == "Felid" or sp == "Troll" then
        return "Unarmed Combat"
    end

    local class = you.class()
    if class == "Hunter" or class == "Hexslinger" then
        return "Ranged Weapons"
    end

    if sp == "Kobold" then
        return "Maces & Flails"
    elseif sp == "Merfolk" then
        return "Polearms"
    elseif sp == "Spriggan" then
        return "Short Blades"
    else
        return "Axes"
    end
end

-- other player functions

function hp_is_low(percentage)
    local hp, mhp = you.hp()
    return 100 * hp <= percentage * mhp
end

function hp_is_full()
    local hp, mhp = you.hp()
    return hp == mhp
end

function meph_immune()
    -- should also check clarity and unbreathing
    return you.res_poison() >= 1
end

function miasma_immune()
    -- this isn't all the cases, I know
    return you.race() == "Gargoyle"
        or you.race() == "Vine Stalker"
        or you.race() == "Ghoul"
        or you.race() == "Mummy"
end

function in_bad_form(include_tree)
    -- These are the forms crawl marks as badform (via is_badform in the form
    -- data) as of DCSS 0.34.
    local form = you.transform()
    return form == "bat"
        or form == "pig"
        or form == "wisp"
        or form == "fungus"
        or form == "jelly"
        or include_tree and form == "tree"
end

function transformed()
    return you.transform() ~= ""
end

-- Forms that meld our weapons as of DCSS 0.34, making us unable to wield.
-- (Most other forms either don't block the weapon slot or aren't reachable
-- for qw.) Note these must match the wiz_name of each form, which
-- you.transform() reports; the serpent form reports itself as
-- "amphisbaena".
const.nowield_forms = {
    ["bat"] = true,
    ["bat swarm"] = true,
    ["dragon"] = true,
    ["fungus"] = true,
    ["jelly"] = true,
    ["pig"] = true,
    ["rime yak"] = true,
    ["amphisbaena"] = true,
    ["sphinx"] = true,
    ["spider"] = true,
    ["storm"] = true,
    ["sun scarab"] = true,
    ["walking scroll"] = true,
    ["wisp"] = true,
}

function unable_to_wield_weapon()
    if you.berserk() or you.race() == "Felid" then
        return true
    end

    return const.nowield_forms[you.transform()] or false
end

function unable_to_swap_weapons()
    if unable_to_wield_weapon() then
        return true
    end

    -- XXX: If we haven't initialized this yet, assume it's unsafe for coglins
    -- to swap weapons.
    if qw.danger_in_los == nil then
        return you.race() == "Coglin"
    end

    return (qw.danger_in_los or not qw.position_is_safe)
        and you.race() == "Coglin"
end

function can_read()
    return not (you.berserk()
        or you.confused()
        or you.silenced()
        or you.status("engulfed (cannot breathe)")
        or you.status("unable to read"))
end

function can_drink()
    return not (you.berserk()
        or you.race() == "Mummy"
        or you.transform() == "lich"
        or you.status("unable to drink"))
end

function can_evoke()
    return not (you.berserk()
        or you.confused()
        or transformed()
        or you.mutation("inability to use devices") > 0)
end

function can_teleport()
    return can_read()
        and not (you.teleporting()
            or you.anchored()
            or you.transform() == "tree"
            or you.race() == "Formicid"
            or in_branch("Gauntlet"))
        and find_item("scroll", "teleportation")
end

function can_use_altars()
    return not (you.berserk()
        or you.silenced()
        or you.status("engulfed (cannot breathe)"))
end

function can_invoke()
    return not (you.berserk()
        or you.confused()
        or you.silenced()
        or you.under_penance(you.god())
        or you.status("engulfed (cannot breathe)"))
end

function can_berserk()
    return not using_ranged_weapon()
        and not intrinsic_undead()
        and you.race() ~= "Formicid"
        and not you.mesmerised()
        and not you.status("afraid")
        and not you.transform() == "lich"
        and not you.status("on berserk cooldown")
        and you.god() == "Trog"
        and you.piety_rank() >= 1
        and can_invoke()
end

function can_use_mp(mp)
    if you.race() == "Djinni" then
        return you.hp() > mp
    else
        return you.mp() >= mp
    end
end

function player_move_delay_func()
    local delay = 10

    local form = you.transform()
    if form == "tree" then
        return const.inf_turns
    elseif form == "bat" then
        delay = 6
    elseif form == "pig" then
        delay = 7
    elseif you.race() == "Spriggan" then
        delay = 6
    elseif you.race() == "Barachi" then
        delay = 12
    elseif you.race() == "Naga" then
        delay = 14
    end

    if you.god() == "Cheibriados" then
        delay = delay + 10
    end

    if form == "statue" then
        delay = 1.5 * delay
    end

    if you.hasted() or you.berserk() then
        delay = 2 / 3 * delay
    end

    if you.slowed() then
        delay = 1.5 * delay
    end

    if view.feature_at(0, 0) == "shallow_water"
            and not (you.flying()
                or you.god() == "Beogh"
                    and you.piety_rank() >= 5)
            and not intrinsic_amphibious() then
        delay = 8 / 5 * delay
    end

    return delay
end

function player_move_delay()
    return turn_memo("player_move_delay", player_move_delay_func)
end

function base_mutation(str)
    return you.mutation(str) - you.temp_mutation(str)
end

function drain_level()
    local drain_levs = { ["lightly drained"] = 1, ["drained"] = 2,
        ["heavily drained"] = 3, ["very heavily drained"] = 4,
        ["extremely drained"] = 5 }
    for s, v in pairs(drain_levs) do
        if you.status(s) then
            return v
        end
    end
    return 0
end

function body_size()
    if you.race() == "Kobold" then
        return -1
    elseif you.race() == "Spriggan" or you.race() == "Felid" then
        return -2
    elseif you.race() == "Troll"
            or you.race() == "Oni"
            or you.race() == "Naga"
            or you.race() == "Armataur" then
        return 1
    else
        return 0
    end
end

function calc_los_radius()
    if you.race() == "Barachi" then
        qw.los_radius = 8
    elseif you.race() == "Kobold" then
        qw.los_radius = 4
    else
        qw.los_radius = 7
    end
end

function unable_to_move()
    return turn_memo("unable_to_move",
        function()
            local form = you.transform()
            return form == "tree" or form == "fungus" and qw.danger_in_los
        end)
end

function dangerous_to_move(allow_spiked)
    return turn_memo_args("dangerous_to_move",
        function()
            return not allow_spiked and you.status("spiked")
                or you.confused()
                    and (check_brothers_in_arms(1)
                        or check_greater_servants(1)
                        or check_divine_warriors(1)
                        or check_beogh_allies(1))
        end, allow_spiked)
end

function unable_to_melee()
    return turn_memo("unable_to_melee",
        function()
            return you.caught()
        end)
end

function unable_to_shoot()
    return turn_memo("unable_to_shoot",
        function()
            if you.berserk() or you.caught() then
                return true
            end

            local form = you.transform()
            return not (form == ""
                or form == "tree"
                or form == "statue"
                or form == "lich")
        end)
end

function unable_to_throw()
    if you.berserk() or you.confused() or you.caught() then
        return true
    end

    local form = you.transform()
    return not (form == ""
        or form == "tree"
        or form == "statue"
        or form == "lich")
end

function player_can_melee_mons(mons)
    if mons:name() == "orb of destruction"
            or mons:attacking_causes_penance()
            or unable_to_melee() then
        return false
    end

    local range = player_reach_range()
    local dist = mons:distance()
    if range == 2 then
        return dist <= range and view.can_reach(mons:x_pos(), mons:y_pos())
    else
        return dist <= range
    end
end

function dangerous_to_shoot()
    return turn_memo("dangerous_to_shoot",
        function()
            return dangerous_to_attack()
                -- Don't attempt to shoot with summoned allies adjacent.
                or you.confused()
                    and (check_brothers_in_arms(qw.los_radius)
                        or check_greater_servants(qw.los_radius)
                        or check_divine_warriors(qw.los_radius)
                        or check_beogh_allies(qw.los_radius))
        end)
end

function dangerous_to_melee()
    return turn_memo("dangerous_to_melee",
        function()
            return dangerous_to_attack()
                -- Don't attempt melee with summoned allies adjacent.
                or you.confused()
                    and (check_brothers_in_arms(1)
                        or check_greater_servants(1)
                        or check_divine_warriors(1)
                        or check_beogh_allies(1))
        end)
end

-- Currently we only use this to disallow attacking when in an exclusion.
function dangerous_to_attack()
    return not map_is_unexcluded_at(qw.map_pos)
end

function want_to_be_surrounded()
    return turn_memo("want_to_be_surrounded",
        function()
            local have_vamp_cleave = false
            for weapon in equipped_slot_iter("weapon") do
                if weapon.weap_skill == "Axes"
                        and weapon:ego() == "vampirism" then
                    have_vamp_cleave = true
                    break
                end
            end
            if not have_vamp_cleave then
                return false
            end

            local vamp_check = function(mons)
                    return not mons:is_immune_vampirism()
                end
            return count_enemies(qw.los_radius, vamp_check) >= 4
        end)
end

function max_strength()
    return select(2, you.strength())
end

function max_dexterity()
    return select(2, you.dexterity())
end
------------------
-- Functions and data related to god worship.

-- God data: name (as reported by you.god()), whether the god uses Invocations,
-- whether the god has abilities that use MP.
--
-- This gets loaded into the god_data table, which is keyed by the god name
-- name. Use the helper functions to access this data: god_full_name(),
-- god_uses_mp(), god_uses_invocations().
local god_data_values = {
    { "No God", false, false },
    { "the Shining One", true, true },
    { "Ashenzari", false, false },
    { "Beogh", true, true },
    { "Cheibriados", true, true },
    { "Dithmenos", true, true },
    { "Elyvilon", true, true },
    { "Fedhas", true, true },
    { "Gozag", false, false },
    { "Hepliaklqana", false, false },
    { "Ignis", false, false },
    { "Jiyva", true, true },
    { "Kikubaaqudgha", false, true },
    { "Lugonu", false, true },
    { "Makhleb", true, false },
    { "Nemelex Xobeh", true, true },
    { "Okawaru", true, true },
    { "Qazlal", true, true },
    { "Ru", false, false },
    { "Sif Muna", true, true },
    { "Trog", false, false },
    { "Uskayaw", true, true },
    { "Vehumet", false, false },
    { "Wu Jian", false, false },
    { "Xom", false, false },
    { "Yredelemnul", true, true },
    { "Zin", true, true },
}

good_gods = { "Elyvilon", "the Shining One", "Zin" }
function is_good_god(god)
    if not god then
        god = you.god()
    end

    return util.contains(good_gods, god)
end

local god_data = {}
local god_lookups = {}
function initialize_god_data()
    const.mp_using_gods = {}

    for _, entry in ipairs(god_data_values) do
        local god = entry[1]
        god_data[god] = {}
        god_data[god]["uses_invocations"] = entry[2]
        god_data[god]["uses_mp"] = entry[3]
        if entry[3] then
            table.insert(const.mp_using_gods, god)
        end

        god_lookups[god:upper()] = god
        if god == "the Shining One" then
            god_lookups["1"] = god
            god_lookups["TSO"] = god
        elseif god == "No God" then
            god_lookups["0"] = god
            god_lookups["None"] = god
        else
            god_lookups[god:sub(1, 1)] = god
            local name = god:sub(1, 3)
            name = trim(name)
            god_lookups[name:upper()] = god

            name = god:sub(1, 4)
            name = trim(name)
            god_lookups[name:upper()] = god
        end
    end
end

function god_full_name(str)
    return god_lookups[str:upper()]
end

function god_uses_mp(god)
    if you.race() == "Djinni" then
        return false
    end

    if not god then
        god = you.god()
    end

    if not god_data[god] then
        return false
    end

    return god_data[god].uses_mp
end

function enough_max_mp_for_god(max_mp, god)
    if you.race() == "Djinni" then
        return true
    end

    -- Hero costs 2 and Finesse costs 5, so we want at least 7mmp
    if god == "Okawaru" then
        return max_mp >= 7
    end

    -- These gods want to spam MP-using abilities .
    if god == "Cheibriados" or god == "the Shining One" then
        return max_mp >= 30
    end

    return true
end

function future_gods_enough_max_mp(max_mp)
    if you.race() == "Djinni" then
        return true
    end

    for _, god in ipairs(qw.future_gods) do
        if not enough_max_mp_for_god(max_mp, god) then
            return false
        end
    end

    return true
end

function item_is_evil(it)
    local subtype = it.subtype()
    if subtype and subtype:find("^demon") then
        return true
    end

    local ego = it.ego()
    if ego == "pain"
            or ego == "vampirism"
            or ego == "draining"
            or ego == "chaos"
            or ego == "reaping"
            or ego == "distortion" then
        return true
    end

    if not subtype then
        return false
    end

    local name = it.name()
    return name:find("Vitality") and subtype:find("^amulet")
        or name:find("{damnation}")
        or name:find("Cerebov") and subtype == "great sword"
        or name:find("Asmodeus") and subtype == "eveningstar"
        or name:find("Cigotuvi's embrace")
        or name:find("Black Knight's barding")
end

function current_god_hates_item(it)
    -- We don't want to be wearing hated items when we convert to a new god,
    -- since we might incur penance while taking them off.
    local new_god
    if goal_status then
        new_god = goal_god(goal_status)
        if new_god and view.feature_at(0, 0) ~= god_altar(new_god) then
            new_god = nil
        end
    end

    return god_hates_item(you.god(), it)
        or new_god and god_hates_item(new_god, it)
end

function god_hates_item(god, it)
    if is_good_god(god) and item_is_evil(it) then
        return true
    end

    local ego = it.ego()
    if god == "Cheibriados" then
        return ego == "speed" or ego == "chaos"
    end

    if god == "Yredelemnul" then
        return ego == "holy wrath"
    end

    if god == "Trog" then
        return ego == "pain"
    end

    return false
end

function future_gods_hate_item(it)
    for _, god in ipairs(qw.future_gods) do
        if god_hates_item(god, it) then
            return true
        end
    end

    return false
end

function altar_god(feat)
    return god_full_name(feat:gsub("^altar_", ""):gsub("_", " "))
end

function god_altar(god)
    if not god then
        god = you.god()
    end

    return "altar_" .. god:lower():gsub(" ", "_")
end

function god_uses_invocations(god)
    if not god then
        god = you.god()
    end

    if not god_data[god] then
        return false
    end

    return god_data[god].uses_invocations
end

function altar_found(god, feat_state)
    if not feat_state then
        feat_state = const.explore.reachable
    end

    if not c_persist.altars[god] then
        return
    end

    for level, entries in pairs(c_persist.altars[god]) do
        for _, state in pairs(entries) do
            if state.feat >= feat_state then
                return level
            end
        end
    end
end

function can_trogs_hand()
    return you.god() == "Trog"
        and you.piety_rank() >= 2
        and can_invoke()
end

function can_brothers_in_arms()
    return you.god() == "Trog"
        and you.piety_rank() >= 4
        and can_invoke()
end


function can_heroism()
    return you.god() == "Okawaru"
        and you.piety_rank() >= 1
        and can_use_mp(2)
        and can_invoke()
end

function can_finesse()
    return you.god() == "Okawaru"
        and you.piety_rank() >= 4
        and can_use_mp(5)
        and can_invoke()
end

function can_recall()
    return (you.god() == "Yredelemnul" and you.piety_rank() >= 2
            or you.god() == "Beogh" and you.piety_rank() >= 2)
        and not you.status("recalling")
        and can_invoke()
end

function can_recall_ancestor()
    return you.god() == "Hepliaklqana"
        and can_use_mp(2)
        and can_invoke()
end

function can_slouch()
    return you.god() == "Cheibriados"
        and you.piety_rank() >= 4
        and can_use_mp(5)
        and can_invoke()
end

function can_ely_healing()
    -- "Heal Self" (formerly "Greater Healing") requires piety rank 2 and 3
    -- MP as of DCSS 0.34.
    return you.god() == "Elyvilon"
        and you.piety_rank() >= 2
        and can_use_mp(3)
        and can_invoke()
end

function can_purification()
    return you.god() == "Elyvilon"
        and you.piety_rank() >= 3
        and can_use_mp(3)
        and can_invoke()
end

function can_recite()
    return you.god() == "Zin"
        and you.piety_rank() >= 1
        and not you.status("reciting")
        and can_invoke()
end

function can_ru_healing()
    return you.god() == "Ru"
        and you.piety_rank() >= 3
        and not you.exhausted()
        and can_invoke()
end

function can_apocalypse()
    return you.god() == "Ru"
        and you.piety_rank() >= 5
        and can_use_mp(8)
        and not you.exhausted()
        and can_invoke()
end

function can_grand_finale()
    return you.god() == "Uskayaw"
        and you.piety_rank() >= 5
        and can_use_mp(8)
        and can_invoke()
end

function can_greater_servant()
    -- The Makhleb rework in DCSS 0.34 renamed "Greater Servant of Makhleb" to
    -- "Infernal Servant", which now costs 8 HP and 4 MP.
    return you.god() == "Makhleb"
        and you.piety_rank() >= 5
        and you.hp() > 10
        and can_use_mp(4)
        and can_invoke()
end

function can_cleansing_flame(ignore_mp)
    return you.god() == "the Shining One"
        and you.piety_rank() >= 3
        and (ignore_mp or can_use_mp(5))
        and can_invoke()
end

function can_divine_warrior(ignore_mp)
    return you.god() == "the Shining One"
        and you.piety_rank() >= 5
        and (ignore_mp or can_use_mp(8))
        and can_invoke()
end

function can_destruction()
    -- The Makhleb rework in DCSS 0.34 renamed "Major Destruction" to "Unleash
    -- Destruction", which now costs roughly 6.5% of max HP plus 2 HP.
    return you.god() == "Makhleb"
        and you.hp() > 6
        and can_invoke()
end

function can_fiery_armour()
    return you.god() == "Ignis"
        and you.piety_rank() >= 1
        and can_invoke()
end

function can_foxfire_swarm()
    return you.god() == "Ignis"
        and you.piety_rank() >= 1
        and can_invoke()
end

function check_allies_func(radius, filter)
    for pos in square_iter(const.origin, radius) do
        local mons = get_monster_at(pos)
        if mons and mons:is_friendly()
                and (not filter or filter(mons)) then
            return true
        end
    end
    return false
end

function check_allies(radius, filter)
    return turn_memo_args("check_allies",
        function()
            return check_allies_func(radius, filter)
        end, radius, filter)
end

function check_brothers_in_arms(radius)
    if you.god() ~= "Trog" then
        return false
    end

    local filter = function (mons)
        return mons:is("summoned")
            and mons:is("berserk")
            and contains_string_in(mons:name(),
                { "ogre", "giant", "bear", "troll" })
    end
    return check_allies(radius, filter)
end

function check_elliptic(radius)
    if you.god() ~= "Hepliaklqana" then
        return false
    end

    local filter = function (mons)
        return mons:is("summoned")
            and contains_string_in(mons:name(), { "elliptic" })
    end
    return check_allies(radius, filter)
end

function check_greater_servants(radius)
    if you.god() ~= "Makhleb" then
        return false
    end

    local filter = function (mons)
        return mons:is("summoned")
            and contains_string_in(mons:name(), { "Executioner", "green death",
                "blizzard demon", "balrug", "cacodemon" })
    end
    return check_allies(radius, filter)
end

function check_divine_warriors(radius)
    if you.god() ~= "the Shining One" then
        return false
    end

    local filter = function (mons)
        return mons:is_summoned()
            and contains_string_in(mons:name(), { "angel", "daeva" })
    end
    return check_allies(radius, filter)
end

function check_beogh_allies(radius)
    if you.god() ~= "Beogh" then
        return false
    end

    local filter = function (mons)
        -- Beogh allies are permanent.
        return not mons:is_summoned()
            and contains_string_in(mons:name(), { "orc" })
    end
    return check_allies(radius, filter)
end

function update_altar(god, level, hash, state, force)
    if state.safe == nil and not state.feat and not state.threat then
        error("Undefined altar state.")
    end

    if not c_persist.altars[god] then
        c_persist.altars[god] = {}
    end

    if not c_persist.altars[god][level] then
        c_persist.altars[god][level] = {}
    end

    local current = c_persist.altars[god][level][hash]
    if not current then
        current = {}
        cleanup_feature_state(current)
        c_persist.altars[god][level][hash] = current
    end

    if state.safe == nil then
        state.safe = current.safe
    end
    if state.feat == nil then
        state.feat = current.feat
    end
    if state.threat == nil then
        state.threat = current.threat
    end

    local feat_state_changed = current.feat < state.feat
            or force and current.feat ~= state.feat
    if state.safe == current.safe
            and not feat_state_changed
            and state.threat == current.threat then
        return false
    end

    if debug_channel("map") then
        dsay("Updating altar on " .. level .. " at "
            .. cell_string_from_map_position(unhash_position(hash))
            .. " from " .. stairs_state_string(current)
            .. " to " .. stairs_state_string(state))
    end

    current.safe = state.safe
    current.threat = state.threat
    if feat_state_changed then
        current.feat = state.feat
        qw.want_goal_update = true
    end

    return true
end

function estimate_slouch_damage()
    local total = 0
    for _, enemy in ipairs(qw.enemy_list) do
        local delay = enemy:move_delay()
        local val = 0
        if delay < 5 then
            val = 3
        elseif delay < 8 then
            val = 2.5
        elseif delay < 10 then
            val = 1.5
        elseif delay == 10 then
            val = 1
        end

        if val > 0 and enemy:threat() <= 1 then
            val = 0.5
        end

        total = total + val
    end
    return total
end

function update_permanent_flight()
    if not gained_permanent_flight then
        return
    end

    for god, levels in pairs(c_persist.altars) do
        for level, altars in pairs(levels) do
            for hash, state in pairs(altars) do
                if state.feat >= const.explore.seen
                        and state.feat < const.explore.reachable then
                    update_altar(god, level, hash,
                        { feat = const.explore.reachable })
                end
            end
        end
    end
end
------------------
-- Skill selection

const.skill_list = {
    "Fighting", "Maces & Flails", "Axes", "Polearms", "Staves",
    "Unarmed Combat", "Throwing", "Short Blades", "Long Blades",
    "Ranged Weapons", "Armour", "Dodging", "Shields", "Stealth",
    "Spellcasting", "Conjurations", "Hexes", "Summonings", "Necromancy",
    "Translocations", "Alchemy", "Fire Magic", "Ice Magic", "Air Magic",
    "Earth Magic", "Invocations", "Evocations", "Shapeshifting",
}

const.ev_value = 0.8
const.ac_value = 1.0
const.sh_value = 0.75
const.delay_value = 2.4

-- start diminishing utility of a defensive stat once you have 25 of it
function diminish(delta, base)
  if base <= 25 then
    return delta
  end
  return delta * 25 / base
end

function weapon_skill()
    -- Cache in case we unwield a weapon somehow.
    if c_persist.weapon_skill then
        return c_persist.weapon_skill
    end

    if you.class() ~= "Wanderer" then
        for weapon in equipped_slot_iter("weapon") do
            if weapon.weap_skill ~= "Short Blades" then
                c_persist.weapon_skill = weapon.weap_skill
                return c_persist.weapon_skill
            end
        end
    end

    c_persist.weapon_skill = weapon_skill_choice()
    return c_persist.weapon_skill
end

function choose_single_skill(chosen_sk)
    you.train_skill(chosen_sk, 1)
    for _, sk in ipairs(const.skill_list) do
        if sk ~= chosen_sk then
            you.train_skill(sk, 0)
        end
    end
end

function shield_skill_utility()
    local shield = get_shield()
    if not shield or shield.encumbrance == 0 then
        return 0
    end
    local sh_gain = 0.19 + shield.ac/40
    local delay_reduction = 2 * shield.encumbrance * shield.encumbrance
        / (25 + 5 * max_strength()) / 27
    local ev_gain = delay_reduction
    return const.sh_value * diminish(sh_gain, you.sh())
        + const.ev_value * diminish(ev_gain, you.ev())
        + const.delay_value * delay_reduction
end

function skill_value(sk)
    if sk == "Dodging" then
        local str = max_strength()
        if str < 1 then
            str = 1
        end

        local evp_adj = max(armour_evp() - 3, 0)
        local penalty_factor
        if evp_adj >= str then
            penalty_factor = str / (2 * evp_adj)
        else
            penalty_factor = 1 - evp_adj / (2 * str)
        end
        if you.race() == "Tengu" and intrinsic_flight() then
            penalty_factor = penalty_factor * 1.2 -- flying EV mult
        end
        local ev_gain = 0.8 * max(you.dexterity(), 1)
            / (20 + 2 * body_size()) * penalty_factor
        return const.ev_value * diminish(ev_gain, you.ev())
    elseif sk == "Armour" then
        local str = max_strength()
        if str < 0 then
            str = 0
        end
        local ac_gain = base_ac() / 22
        local ev_gain = 2 / 225 * armour_evp() ^ 2 / (3 + str)
        return const.ac_value * diminish(ac_gain, you.ac())
            + const.ev_value * diminish(ev_gain, you.ev())
    elseif sk == "Fighting" then
        return 0.75
    elseif sk == "Shields" then
        return shield_skill_utility()
    elseif sk == "Throwing" then
        local missile = best_missile(missile_damage)
        if missile then
            return missile_damage(missile) / 25
        else
            return 0
        end
    elseif sk == "Invocations" then
        if you.god() == "the Shining One" then
            return undead_or_demon_branch_soon() and 1.5 or 0.5
        elseif you.god() == "Uskayaw" or you.god() == "Zin" then
            return 0.75
        elseif you.god() == "Elyvilon" then
            return 0.5
        else
            return 0
        end
    elseif sk == weapon_skill() then
        local val = at_min_delay() and 0.3 or 1.5
        if weapon_skill() == "Unarmed Combat" then
            sklev = you.skill("Unarmed Combat")
            if sklev > 18 then
                val = val * 18 / sklev
            end
        end
        return val
    end
end

function choose_skills()
    -- Choose one martial skill to train.
    local martial_skills = { weapon_skill(), "Fighting", "Shields", "Armour",
        "Dodging", "Invocations", "Throwing" }

    local best_sk, best_val
    for _, sk in ipairs(martial_skills) do
        if you.skill_cost(sk) then
            local val = skill_value(sk) / you.skill_cost(sk)
            if val and (not best_val or val > best_val) then
                best_val = val
                best_sk = sk
            end
        end
    end

    local skills = {}
    if best_val then
        if debug_channel("skills") then
            dsay("Best skill: " .. best_sk .. ", value: " .. best_val)
        end

        table.insert(skills, best_sk)
    end

    -- Choose one MP skill to train.
    local mp_skill = "Evocations"
    if god_uses_invocations() then
        mp_skill = "Invocations"
    elseif you.god() == "Ru" or you.god() == "Xom" then
        mp_skill = "Spellcasting"
    end
    local mp_skill_level = you.base_skill(mp_skill)

    if you.god() == "Makhleb"
            and you.piety_rank() >= 2
            and mp_skill_level < 15 then
        table.insert(skills, mp_skill)
    elseif you.god() == "Okawaru"
            and you.piety_rank() >= 1
            and mp_skill_level < 4 then
        table.insert(skills, mp_skill)
    elseif you.god() == "Okawaru"
            and you.piety_rank() >= 4
            and mp_skill_level < 10 then
        table.insert(skills, mp_skill)
    elseif you.god() == "Cheibriados"
            and you.piety_rank() >= 5
            and mp_skill_level < 8 then
        table.insert(skills, mp_skill)
    elseif you.god() == "Yredelemnul"
            and you.piety_rank() >= 4
            and mp_skill_level < 8 then
        table.insert(skills, mp_skill)
    elseif you.race() == "Vine Stalker"
            and you.god() ~= "No God"
            and mp_skill_level < 12
            and (at_min_delay()
                 or you.base_skill(weapon_skill()) >= 3 * mp_skill_level) then
        table.insert(skills, mp_skill)
    end

    local trainable_skills = {}
    local safe_count = 0
    for _, sk in ipairs(skills) do
        if you.can_train_skill(sk) and you.base_skill(sk) < 27 then
            table.insert(trainable_skills, sk)
            if you.base_skill(sk) < 26.5 then
                safe_count = safe_count + 1
            end
        end
    end

    -- Try to avoid getting stuck in the skill screen.
    if safe_count == 0 then
        if you.base_skill("Fighting") < 26.5 then
            table.insert(trainable_skills, "Fighting")
        elseif you.base_skill(mp_skill) < 26.5 then
            table.insert(trainable_skills, mp_skill)
        else
            for _, sk in ipairs(const.skill_list) do
                if you.can_train_skill(sk) and you.base_skill(sk) < 26.5 then
                    table.insert(trainable_skills, sk)
                    return trainable_skills
                end
            end
        end
    end
    return trainable_skills
end

function handle_skills()
    skills = choose_skills()
    choose_single_skill(skills[1])
    for _, sk in ipairs(skills) do
        you.train_skill(sk, 1)
    end
end

function update_skill_tracking()
    if not qw.base_skills then
        qw.base_skills = {}
    end

    for _, sk in ipairs(const.skill_list) do
        local base_skill = you.base_skill(sk)
        if base_skill > 0
                and (not qw.base_skills[sk]
                    or base_skill - qw.base_skills[sk] >= 1) then
            reset_best_equip()
            qw.base_skills[sk] = base_skill
        end
    end
end

function choose_stat_gain()
    local ap = armour_plan()
    if ap == "heavy" or ap == "large" then
        return "s"
    elseif ap == "light" then
        return "d"
    else
        if 3 * max_strength() < 2 * max_dexterity() then
            return "s"
        else
            return "d"
        end
    end
end

-- clua hook for experience menu after quaffing !experience. Simply accepts the
-- default skill allocations.
function auto_experience()
    return true
end
------------------
-- Stair-related functions

-- Stair direction enum
const.dir = { up = -1, down = 1 }

const.inf_dist = 10000

const.upstairs = {
    "stone_stairs_up_i",
    "stone_stairs_up_ii",
    "stone_stairs_up_iii",
}

const.downstairs = {
    "stone_stairs_down_i",
    "stone_stairs_down_ii",
    "stone_stairs_down_iii",
}

const.escape_hatches = {
    [const.dir.up] = "escape_hatch_up",
    [const.dir.down] = "escape_hatch_down",
}

function dir_key(dir)
    return dir == const.dir.down and ">"
        or (dir == const.dir.up and "<" or nil)
end

--[[
Return a list of stair features we're allowed to take on the given level and in
the given direction that takes us to the next depth for that direction. For
going up, this includes branch exits that take us out of the branch. Up escape
hatches are included on the Orb run under the right conditions. For going down,
this does not include any branch entrances, but does include features in Abyss
and Pan that lead to the next level in the branch.
--]]
function level_stairs_features(branch, depth, dir)
    local feats
    if dir == const.dir.up then
        if is_portal_branch(branch)
                or branch == "Abyss"
                or is_hell_branch(branch)
                or depth == 1 then
            feats = { branch_exit(branch) }
        else
            feats = util.copy_table(const.upstairs)
        end

        if want_to_use_escape_hatches(const.dir.up) then
            table.insert(feats, "escape_hatch_up")
        end
    elseif dir == const.dir.down then
        if branch == "Abyss" and depth < branch_depth("Abyss") then
            feats = { "abyssal_stair" }
        elseif branch == "Pan" then
            feats = { "transit_pandemonium" }
        elseif is_hell_branch(branch) and depth < branch_depth(branch) then
            feats = { const.downstairs[1] }
        elseif depth < branch_depth(branch) then
            feats = util.copy_table(const.downstairs)
        end
    end
    return feats
end

function stairs_state_string(state)
    return enum_string(state.feat, const.explore) .. "/"
        .. (state.safe and "safe" or "unsafe") .. "/"
        .. "threat:" .. tostring(state.threat)
end

function update_stone_stairs(branch, depth, dir, num, state, force)
    if state.safe == nil and not state.feat and not state.threat then
        error("Undefined stone stairs state.")
    end

    local data
    if dir == const.dir.down then
        data = c_persist.downstairs
    else
        data = c_persist.upstairs
    end

    local level = make_level(branch, depth)
    if not data[level] then
        data[level] = {}
    end

    local current = data[level][num]
    if not current then
        current = {}
        cleanup_feature_state(current)
        data[level][num] = current
    end

    if state.safe == nil then
        state.safe = current.safe
    end
    if state.feat == nil then
        state.feat = current.feat
    end
    if state.threat == nil then
        state.threat = current.threat
    end

    local feat_state_changed = current.feat < state.feat
            or force and current.feat ~= state.feat
    if state.safe == current.safe
            and not feat_state_changed
            and state.threat == current.threat then
        return
    end

    if debug_channel("map") then
        dsay("Updating stone " .. (dir == const.dir.up and "up" or "down")
            .. "stairs " .. num .. " on " .. level
            .. " from " .. stairs_state_string(current) .. " to "
            .. stairs_state_string(state))
    end

    current.safe = state.safe
    current.threat = state.threat
    if feat_state_changed then
        current.feat = state.feat
        qw.want_goal_update = true
    end
end

function update_all_stone_stairs(branch, depth, dir, state, max_feat_state)
    for i = 1, num_required_stairs(branch, depth, dir) do
        local num = ("i"):rep(i)
        local cur_state = get_stone_stairs(branch, depth, dir, num)
        if cur_state and (not max_feat_state
                or cur_state.feat >= state.feat) then
            update_stone_stairs(branch, depth, dir, num, state, true)
        end
    end
end

function reset_stone_stairs(branch, depth, dir)
    update_all_stone_stairs(branch, depth, dir,
        { feat = const.explore.reachable }, true)

    local level = make_level(branch, depth)
    if level == where then
        map_mode_searches[dir_key(dir)] = nil
    elseif level == previous_where then
        map_mode_searches_cache[3 - cache_parity][dir_key(dir)] = nil
    end

    if where ~= level then
        reset_autoexplore(level)
    end
end

function get_stone_stairs(branch, depth, dir, num)
    local level = make_level(branch, depth)
    if dir == const.dir.up then
        if not c_persist.upstairs[level]
                or not c_persist.upstairs[level][num] then
            return
        end

        return c_persist.upstairs[level][num]
    elseif dir == const.dir.down then
        if not c_persist.downstairs[level]
                or not c_persist.downstairs[level][num] then
            return
        end

        return c_persist.downstairs[level][num]
    end
end

function num_required_stairs(branch, depth, dir)
    if dir == const.dir.up then
        if depth == 1
                or is_portal_branch(branch)
                or branch == "Tomb"
                or branch == "Abyss"
                or branch == "Pan"
                or is_hell_branch(branch) then
            return 0
        else
            return 3
        end
    elseif dir == const.dir.down then
        if depth == branch_depth(branch)
                    or is_portal_branch(branch)
                    or branch == "Tomb"
                    or branch == "Abyss"
                    or branch == "Pan" then
            return 0
        elseif is_hell_branch(branch) then
            return 1
        else
            return 3
        end
    end
end

function count_stairs(branch, depth, dir, feat_state)
    local num_required = num_required_stairs(branch, depth, dir)
    if num_required == 0 then
        return 0
    end

    local count = 0
    for i = 1, num_required do
        local num = ("i"):rep(i)
        local state = get_stone_stairs(branch, depth, dir, num)
        if state and state.feat >= feat_state then
            count = count + 1
        end
    end
    return count
end

function have_all_stairs(branch, depth, dir, feat_state)
    local num_required = num_required_stairs(branch, depth, dir)
    if num_required > 0 then
        for i = 1, num_required do
            local num = ("i"):rep(i)
            local state = get_stone_stairs(branch, depth, dir, num)
            if not state or state.feat < feat_state then
                return false
            end
        end
    end

    return true
end

function update_branch_stairs(branch, depth, dest_branch, dir, state, force)
    if state.safe == nil and not state.feat and not state.threat then
        error("Undefined branch stairs state.")
    end

    local data = dir == const.dir.down and c_persist.branch_entries
        or c_persist.branch_exits
    if not data[dest_branch] then
        data[dest_branch] = {}
    end

    local level = make_level(branch, depth)
    local current = data[dest_branch][level]
    if not current then
        current = {}
        cleanup_feature_state(current)
        data[dest_branch][level] = current
    end

    if state.safe == nil then
        state.safe = current.safe
    end
    if state.feat == nil then
        state.feat = current.feat
    end
    if state.threat == nil then
        state.threat = current.threat
    end

    local feat_state_changed = current.feat < state.feat
        or force and current.feat ~= state.feat
    if state.safe == current.safe
            and not feat_state_changed
            and state.threat == current.threat then
        return
    end

    if debug_channel("map") then
        dsay("Updating " .. dest_branch .. " branch "
            .. (dir == const.dir.up and "exit" or "entrance") .. " stairs "
            .. " on " .. level .. " from " .. stairs_state_string(current)
            .. " to " .. stairs_state_string(state))
    end

    current.safe = state.safe
    current.feat = state.feat
    current.threat = state.threat

    if not feat_state_changed then
        return
    end

    if dir == const.dir.down then
        -- Update the entry depth in the branch data with the depth where
        -- we found this entry if the entry depth is currently unconfirmed
        -- or if the found depth is higher.
        local parent_br, parent_min, parent_max = parent_branch(dest_branch)
        if branch == parent_br
                and (parent_min ~= parent_max or depth < parent_min) then
            branch_data[dest_branch].parent_min_depth = depth
            branch_data[dest_branch].parent_max_depth = depth
        end
    end

    qw.want_goal_update = true
end

function update_escape_hatch(branch, depth, dir, hash, state, force)
    if state.safe == nil and not state.feat and not state.threat then
        error("Undefined escape hatch state.")
    end

    local data
    if dir == const.dir.down then
        data = c_persist.down_hatches
    else
        data = c_persist.up_hatches
    end

    local level = make_level(branch, depth)
    if not data[level] then
        data[level] = {}
    end

    local current = data[level][hash]
    if not current then
        current = {}
        cleanup_feature_state(current)
        data[level][hash] = current
    end

    if state.safe == nil then
        state.safe = current.safe
    end
    if state.feat == nil then
        state.feat = current.feat
    end
    if state.threat == nil then
        state.threat = current.threat
    end

    local feat_state_changed = current.feat < state.feat
            or force and current.feat ~= state.feat
    if state.safe == current.safe
            and not feat_state_changed
            and state.threat == current.threat then
        return
    end

    if debug_channel("map") then
        dsay("Updating escape hatch " .. " on " .. level .. " at "
            .. cell_string_from_map_position(unhash_position(hash))
            .. " from " .. stairs_state_string(current) .. " to "
            .. stairs_state_string(state))
    end

    current.safe = state.safe
    current.feat = state.feat
    current.threat = state.threat
end

function get_map_escape_hatch(branch, depth, pos)
    local level = make_level(branch, depth)
    local hash = hash_position(pos)
    if c_persist.up_hatches[level] and c_persist.up_hatches[level][hash] then
        return c_persist.up_hatches[level][hash]
    elseif c_persist.down_hatches[level]
            and c_persist.down_hatches[level][hash] then
        return c_persist.down_hatches[level][hash]
    end
end

function update_pan_transit(hash, state, force)
    if state.safe == nil and not state.feat and not state.threat then
        error("Undefined Pan transit state.")
    end

    local current = c_persist.pan_transits[hash]
    if not current then
        current = {}
        cleanup_feature_state(current)
        c_persist.pan_transits[hash] = current
    end

    if state.safe == nil then
        state.safe = current.safe
    end
    if state.feat == nil then
        state.feat = current.feat
    end
    if state.threat == nil then
        state.threat = current.threat
    end

    local feat_state_changed = current.feat < state.feat
            or force and current.feat ~= state.feat
    if state.safe == current.safe
            and not feat_state_changed
            and state.threat == current.threat then
        return
    end

    if debug_channel("map") then
        dsay("Updating Pan transit at "
            .. los_pos_string(unhash_position(hash)) .. " from "
            .. stairs_state_string(current) .. " to "
            .. stairs_state_string(state))
    end

    current.safe = state.safe
    current.feat = state.feat
    current.threat = state.threat
end

function get_map_pan_transit(pos)
    return c_persist.pan_transits[hash_position(pos)]
end

function update_abyssal_stairs(hash, state, force)
    if state.safe == nil and not state.feat and not state.threat then
        error("Undefined Abyssal stairs state.")
    end

    local current = c_persist.abyssal_stairs[hash]
    if not current then
        current = {}
        cleanup_feature_state(current)
        c_persist.abyssal_stairs[hash] = current
    end

    if state.safe == nil then
        state.safe = current.safe
    end
    if state.feat == nil then
        state.feat = current.feat
    end
    if state.threat == nil then
        state.threat = current.threat
    end

    local feat_state_changed = current.feat < state.feat
            or force and current.feat ~= state.feat
    if state.safe == current.safe
            and not feat_state_changed
            and state.threat == current.threat then
        return
    end

    if debug_channel("map") then
        dsay("Updating Abyssal stairs at "
            .. los_pos_string(unhash_position(hash)) .. " from "
            .. stairs_state_string(current) .. " to "
            .. stairs_state_string(state))
    end

    current.safe = state.safe
    current.threat = state.threat
    if feat_state_changed then
        current.feat = state.feat
    end
end

function get_map_abyssal_stairs(pos)
    return c_persist.abyssal_stairs[hash_position(pos)]
end

function get_branch_stairs(branch, depth, stairs_branch, dir)
    local level = make_level(branch, depth)
    if dir == const.dir.up then
        if not c_persist.branch_exits[stairs_branch]
                or not c_persist.branch_exits[stairs_branch][level] then
            return
        end

        return c_persist.branch_exits[stairs_branch][level]
    elseif dir == const.dir.down then
        if not c_persist.branch_entries[stairs_branch]
                or not c_persist.branch_entries[stairs_branch][level] then
            return
        end

        return c_persist.branch_entries[stairs_branch][level]
    end
end

function get_destination_stairs(branch, depth, feat)
    local dir, num = stone_stairs_type(feat)
    if dir then
        return get_stone_stairs(branch, depth + dir, -dir, num)
    end

    local branch, dir = branch_stairs_type(feat)
    if branch then
        if dir == const.dir.up then
            local parent, min_depth, max_depth = parent_branch(branch)
            if parent and min_depth == max_depth then
                return get_branch_stairs(parent, min_depth, branch, -dir)
            end
        else
            return get_branch_stairs(branch, 1, branch, -dir)
        end
    end
end

function get_stairs(branch, depth, feat)
    local dir, num = stone_stairs_type(feat)
    if dir then
        return get_stone_stairs(branch, depth, dir, num)
    end

    local branch, dir = branch_stairs_type(feat)
    if branch then
        return get_branch_stairs(where_branch, where_depth, branch, dir)
    end
end
------------------
-- Terrain data and functions.

-- Feature exploration state enum
const.explore = {
    "none",
    "seen",
    "diggable",
    "reachable",
    "explored",
}

function get_feature_name(where_name)
    for _, value in ipairs(portal_data) do
        if where_name == value[1] then
            return value[3]
        end
    end
end

function feature_is_traversable(feat, assume_flight)
    -- XXX: Can we pass a default nil value instead?
    return travel.feature_traversable(feat, assume_flight and true or false)
            and not feature_is_runed_door(feat)
        or feat:find("^trap") ~= nil
end

function feature_is_diggable(feat)
    return feat == "rock_wall"
        or feat == "clear_rock_wall"
        or feat == "slimy_wall"
        or feat == "iron_grate"
        or feat == "granite_statue"
end

function cloud_is_safe(cloud)
    if not cloud then
        return true
    end

    if cloud == "flame"
            or cloud == "freezing vapour"
            or cloud == "thunder"
            or cloud == "acidic fog"
            or cloud == "seething chaos"
            or cloud == "mutagenic fog" then
        return false
    end

    if cloud == "steam" then
        return you.res_fire() > 0
    elseif cloud == "noxious fumes" then
        return meph_immune()
    elseif cloud == "poison gas" then
        return you.res_poison() > 0
    elseif cloud == "foul pestilence" then
        return miasma_immune()
    elseif cloud == "calcifying dust" then
        return you.race() == "Gargoyle" or you.transform() == "statue"
    elseif cloud == "excruciating misery" then
        return intrinsic_undead()
    end

    return true
end

function cloud_is_dangerous(cloud)
    if not cloud then
        return false
    end

    -- We require full safety if no monsters are around.
    if not qw.danger_in_los then
        return not cloud_is_safe(cloud)
    end

    -- We'll still take damage from these with a level of resistance, but
    -- don't consider that dangerous.
    if cloud == "flame" then
        return you.res_fire() < 1
    elseif cloud == "freezing vapour" then
        return you.res_cold() < 1
    elseif cloud == "thunder" then
        return you.res_shock() < 1
    end

    return not cloud_is_safe(cloud)
end

function cloud_is_dangerous_at(pos)
    return cloud_is_dangerous(view.cloud_at(pos.x, pos.y))
end

-- Hook to determine which traps are safe to move over without requiring an
-- answer to a yesno prompt. This can be conditionally disabled with
-- qw.ignore_traps, e.g. as we do on Zot:5.
--
-- XXX: We have to mark Zot traps as safe so we don't get the prompt, as
-- c_answer_prompt isn't called in that case. Should have the crawl
-- yes_or_no() function call c_answer_prompt to fix this.
function c_trap_is_safe(trap)
    if not trap then
        return true
    end

    trap = trap:lower()
    return qw.ignore_traps
        or trap == "zot"
        or you.race() == "Formicid"
            and (trap == "permanent teleport" or trap == "dispersal")
end

function trap_is_safe_at(pos)
    -- A trap is always safe if we're already standing on it.
    if positions_equal(pos, const.origin) then
        return true
    end

    local feat = view.feature_at(pos.x, pos.y)
    if not feat:find("^trap_") then
        return true
    end

    local trap = feat:gsub("trap_", "")
    return c_trap_is_safe(trap) and trap ~= "zot"
end

function is_safe_at(pos, assume_flight)
    local map_pos = position_sum(qw.map_pos, pos)
    if not map_is_unexcluded_at(map_pos) then
        return false
    end

    if assume_flight then
        local feat = view.feature_at(pos.x, pos.y)
        if not feature_is_traversable(feat, true) then
            return false
        end
    elseif not map_is_traversable_at(map_pos) then
        return false
    end

    local cloud = view.cloud_at(pos.x, pos.y)
    if not cloud_is_safe(cloud) then
        return false
    end

    return trap_is_safe_at(pos)
end

function is_cornerish_at(pos)
    if is_traversable_at({ x = pos.x + 1, y = pos.y + 1 })
            or is_traversable_at({ x = pos.x + 1, y = pos.y - 1 })
            or is_traversable_at({ x = pos.x - 1, y = pos.y + 1 })
            or is_traversable_at({ x = pos.x - 1, y = pos.y - 1 }) then
        return false
    end

    return (is_traversable_at({ x = pos.x + 1, y = pos.y })
            or is_traversable_at({ x = pos.x - 1, y = pos.y }))
        and (is_traversable_at({ x = pos.x, y = pos.y + 1 })
            or is_traversable_at({ x = pos.x, y = pos.y - 1 }))
end

function count_adjacent_slimy_walls_at(pos)
    -- No need to count if we've never spotted a wall on the level during a map update.
    if not qw.have_slimy_walls then
        return 0
    end

    local count = 0
    for apos in adjacent_iter(pos) do
        if view.feature_at(apos.x, apos.y) == "slimy_wall" then
            count = count + 1
        end
    end
    return count
end

function is_solid_at(pos, exclude_doors)
    local feat = view.feature_at(pos.x, pos.y)
    return (feat == "unseen" or travel.feature_solid(feat))
        and (not exclude_doors
            or feat ~= "closed_door" and feat ~= "closed_clear_door")
end

function feature_destroys_items(feat)
    return feat == "deep_water" and not intrinsic_amphibious()
        or feat == "lava"
end

function destroys_items_at(pos)
    return feature_destroys_items(view.feature_at(pos.x, pos.y))
end

function feature_is_upstairs(feat)
    return feat:find("^stone_stairs_up") or feat:find("^exit_")
end

function feature_is_downstairs(feat)
    return feat:find("^stone_stairs_down")
end

function feature_is_runed_door(feat)
    return feat == "runed_clear_door" or feat == "runed_door"
end

function feature_uses_map_key(key, feat)
    local dir = stone_stairs_type(feat)
    if not dir then
        dir = select(2, branch_stairs_type(feat))
    end

    if key == ">" then
        return dir and dir == const.dir.down
            or feat == "transporter"
            or feat == "escape_hatch_down"
    elseif key == "<" then
        return dir and dir == const.dir.up
            or feat == "escape_hatch_up"
    else
        return false
    end
end

function feature_is_critical(feat)
    return feature_uses_map_key(">", feat)
        or feature_uses_map_key("<", feat)
        or feat:find("_shop")
        or feat:find("altar_")
        or feat:find("transporter")
        or feat:find("transit")
        or feat:find("abyss")
end

function stone_stairs_type(feat)
    local dir
    if feat:find("^stone_stairs_down") then
        dir = const.dir.down
    elseif feat:find("^stone_stairs_up") then
        dir = const.dir.up
    else
        return
    end

    local num = feat:gsub("stone_stairs_"
        .. (dir == const.dir.down and "down_" or "up_"), "", 1)
    return dir, num
end

function branch_stairs_type(feat)
    local dir
    if feat:find("^enter_") then
        dir = const.dir.down
    elseif feat:find("^exit_") then
        dir = const.dir.up
    else
        return
    end

    if feat == branch_exit("D") then
        return "D", dir
    end

    local entry_feat = feat:gsub("exit", "enter", 1)
    for branch, entry in pairs(branch_data) do
        if entry.entrance == entry_feat then
            return branch, dir
        end
    end
end

function escape_hatch_type(feat)
    if feat == "escape_hatch_up" then
        return const.dir.up
    elseif feat == "escape_hatch_down" then
        return const.dir.down
    end
end

function in_water_at(pos)
    return not (you.flying()
            or you.god() == "Beogh" and you.piety_rank() >= 5)
        and view.feature_at(pos.x, pos.y) == "shallow_water"
end
------------------
-- Travel planning

-- Go up from branch, tracking parent branches and their entries to the child
-- branches we came from.
function parent_branch_chain(branch, check_branch, check_entries)
    if branch == "D" then
        return
    end

    local parents = {}
    local entries = {}
    local cur_branch = branch
    local stop_search = false
    while cur_branch ~= "D" and not stop_search do
        local parent, min_depth = parent_branch(cur_branch)

        if check_branch == parent
                or check_entries and check_entries[parent] then
            stop_search = true
        end

        -- Travel into the branch assuming we enter from min_depth. If this
        -- ends up being our stopping point because we haven't found the
        -- branch, this will be handled later in update_goal_travel().
        entries[parent] = min_depth
        table.insert(parents, parent)
        cur_branch = parent
    end

    return parents, entries
end

function travel_branch_levels(result, dest_depth)
    local dir = sign(dest_depth - result.depth)
    if dir ~= 0 and not result.first_dir and not result.first_branch then
        result.first_dir = dir
    end

    while result.depth ~= dest_depth do
        if count_stairs(result.branch, result.depth, dir,
                const.explore.seen) == 0 then
            return
        end

        result.depth = result.depth + dir
    end
end

function travel_up_branches(result, parents, entries, dest_branch)
    if not result.first_dir and not result.first_branch then
        result.first_dir = const.dir.up
    end

    local i = 1
    for i = 1, #parents do
        if result.branch == dest_branch then
            return
        end

        if is_hell_branch(result.branch) then
            if not branch_found(result.branch, const.explore.reachable)
                    or parents[i] ~= parent_branch(result.branch) then
                return
            end
        else
            travel_branch_levels(result, 1)
            if result.depth ~= 1 then
                return
            end
        end

        result.branch = parents[i]
        result.depth = entries[result.branch]
    end
end

function travel_down_branches(result, dest_branch, dest_depth, parents,
        entries)
    local i = #parents
    for i = #parents, 1, -1 do
        result.branch = parents[i]
        result.depth = entries[result.branch]

        local next_branch, next_depth
        if i > 1 then
            next_branch = parents[i - 1]
            next_depth = entries[next_branch]
        else
            next_branch = dest_branch
            next_depth = dest_depth
        end

        if not result.first_dir and not result.first_branch then
            result.first_branch = next_branch
        end

        -- We stop if we haven't found the next branch or if we can't actually
        -- enter it with travel.
        if not branch_found(next_branch, const.explore.reachable)
                or not branch_travel(next_branch) then
            result.stop_branch = next_branch
            break
        end

        result.branch = next_branch
        result.depth = 1

        travel_branch_levels(result, next_depth)
        if result.depth ~= next_depth then
            break
        end

        i = i - 1
    end
end

--[[
Search branch and stair data from a starting level to a destination level,
returning the furthest point to which we know we can travel.
@string  start_branch The starting branch. Defaults to the current branch.
@int     start_depth  The starting depth. Defaults to the current depth.
@string  dest_branch  The destination branch.
@int     dest_depth   The destination depth.
@treturn table        The travel search results. A table that always
                      contains keys 'branch' and 'depth' containing the
                      furthest level reached. If a 'stairs_dir' key is
                      present, we should do a map mode stairs search to take
                      unexplored stairs in the given direction. If the
                      travel destination is not the current level, the table
                      will have either a key of 'first_dir' indicating the
                      first stair direction we should take during travel, or
                      a key of 'first_branch' indicating that we should
                      first proceed into the given branch. These two values
                      are used by movement plans when we're stuck.
--]]
function travel_destination_search(dest_branch, dest_depth, start_branch,
        start_depth)
    if not start_branch then
        start_branch = where_branch
    end
    if not start_depth then
        start_depth = where_depth
    end
    local result = { branch = start_branch, depth = start_depth }

    -- We're already there.
    if start_branch == dest_branch and start_depth == dest_depth then
        return result
    end

    local common_parent, start_parents, start_entries, dest_parents,
        dest_entries
    if start_branch == dest_branch
            and not (is_hell_branch(start_branch)
                and start_depth > dest_depth) then
        common_parent = start_branch
    else
        start_parents, start_entries = parent_branch_chain(start_branch,
            dest_branch)
        dest_parents, dest_entries = parent_branch_chain(dest_branch,
            start_branch, start_entries)
        if dest_parents then
            common_parent = dest_parents[#dest_parents]
        else
            common_parent = "D"
        end
    end

    -- Travel up and out of the starting branch until we reach the common
    -- parent branch. Don't bother traveling up if the destination branch is a
    -- sub-branch of the starting branch.
    if start_branch ~= common_parent then
        travel_up_branches(result, start_parents, start_entries, common_parent)

        -- We weren't able to travel all the way up to the common parent.
        if result.depth ~= start_entries[common_parent] then
            return result
        end
    end

    -- We've already arrived at our ultimate destination.
    if result.branch == dest_branch and result.depth == dest_depth then
        return result
    end

    -- We're now in the nearest branch in the chain of parent branches of our
    -- starting branch that is also in the chain of parent branches containing
    -- the destination branch. Travel in this nearest branch to the depth of
    -- the first branch entry we'll need to take to start descending to our
    -- destination.
    local next_depth
    if common_parent == dest_branch then
        next_depth = dest_depth
    else
        next_depth = dest_entries[common_parent]
    end
    travel_branch_levels(result, next_depth)

    -- We couldn't make it to the branch entry we need or we already arrived at
    -- our ultimate destination.
    if result.depth ~= next_depth
            or result.branch == dest_branch and result.depth == dest_depth then
        return result
    end

    -- Travel into and down branches to reach our ultimate destination. We're
    -- always starting at the first branch entry we'll need to take.
    travel_down_branches(result, dest_branch, dest_depth, dest_parents,
        dest_entries)
    return result
end

function travel_opens_runed_doors(result)
    if result.stop_branch == "Pan"
                and not branch_found("Pan", const.explore.reachable)
            or result.stop_branch == "Slime"
                and branch_found("Slime")
                and not branch_found("Slime", const.explore.reachable) then
        local parent, min_depth, max_depth = parent_branch(result.stop_branch)
        local level = make_level(result.branch, result.depth)
        return result.branch == parent
            and result.depth >= min_depth
            and result.depth <= max_depth
    end

    return false
end

function travel_safe_stairs(result)
    -- We only consider taking stair safety when taking downstairs or branch
    -- entries. Taking alternate upstairs would be far less useful generally,
    -- and fleeing doesn't yet support fleeing to downstairs, which would be
    -- necessary before we could take alternate upstairs.
    if qw.safe_stairs_failed
            or result.stairs_dir
            or where_branch == result.branch
                and where_depth >= result.depth then
        return
    end

    local best_stairs, best_threat, best_safe, worst_threat
    local stairs = level_stairs_features(result.branch, result.depth, const.dir.up)
    local level = make_level(result.branch, result.depth)
    for _, feat in ipairs(stairs) do
        -- If the stairs are unknown, assume a threat of 0.
        local state = get_stairs(result.branch, result.depth, feat)
        local threat = 0
        -- Unknown stairs are safe.
        local safe = true
        if state then
            threat = state.threat
            safe = state.safe
        -- We're arriving to the Vaults:$ ambush, which is guaranteed to have
        -- 25 vaults guards.
        elseif level == vaults_end then
            threat = 25
        -- We prefer taking stairs that have a known but low threat over taking
        -- unknown ones. So assume unknown stairs have high threat.
        else
            threat = high_threat_level()
        end

        if not worst_threat or threat > worst_threat then
            worst_threat = threat
        end

        local dest_feat = feat
        if result.depth > 1 then
            dest_feat = dest_feat:gsub("_up_", "_down_", 1)
        else
            dest_feat = branch_entrance(result.branch)
        end
        local dest_state = get_destination_stairs(result.branch, result.depth, feat)
        safe = safe and dest_state and dest_state.safe
        if (not best_safe or safe)
                and (not best_threat or threat < best_threat) then
            best_stairs = dest_feat
            best_threat = threat
            best_safe = safe
        end
    end

    -- If no stair has enough threat that we need to buff, we don't need to
    -- take safe stairs.
    if worst_threat < high_threat_level()
            -- If all stairs have equally bad threat and we don't need to
            -- teleport, don't use safe stairs. This will most commonly happen
            -- when all stairs at the destination are unknown.
            or (best_threat == worst_threat
                and best_threat < extreme_threat_level()) then
        return
    end

    -- If the best destination stair threat is high enough, we try to use down
    -- hatches to reach the level.
    local hatches, best_hash
    if best_threat >= extreme_threat_level() and result.depth > 1 then
        local prev_level = make_level(result.branch, result.depth - 1)
        hatches = c_persist.down_hatches[prev_level]
    end
    if hatches then
        for hash, state in pairs(hatches) do
            if not best_safe or state.safe then
                best_hash = hash
                best_safe = state.safe

                -- Stop if we find a safe hatch.
                if best_safe then
                    break
                end
            end
        end
    end

    if best_hash then
        result.safe_hatch = best_hash
    elseif best_stairs then
        result.safe_stairs = best_stairs
    else
        return
    end

    result.depth = result.depth - 1
end

function finalize_first_dir(result)
    if where_branch == result.branch then
        if where_depth == result.depth then
            result.first_dir = nil
        else
            result.first_dir = sign(result.depth - where_depth)
        end
    end
end

function finalize_depth_dir(result, dir)
    assert(type(dir) == "number" and abs(dir) == 1,
        "Invalid stair direction: " .. tostring(dir))

    -- We can already reach all required stairs in the given direction on the
    -- target level, so there's nothing to do in that direction.
    if count_stairs(result.branch, result.depth, dir,
                const.explore.reachable)
            == num_required_stairs(result.branch, depth, dir) then
        return false
    end

    local dir_depth = result.depth + dir
    local dir_depth_stairs = count_stairs(result.branch, dir_depth, -dir,
            const.explore.explored)
        < count_stairs(result.branch, dir_depth, -dir,
            const.explore.reachable)
    -- The level in the given direction isn't autoexplored, so we start there.
    if not autoexplored_level(result.branch, dir_depth) then
        result.depth = dir_depth

        -- If we haven't fully explored explored this level but we already see
        -- there are unexplored stairs, take those before finishing
        -- autoexplore.
        if dir_depth_stairs then
            result.stairs_dir = -dir
        end

        finalize_first_dir(result)
        return true
    end

    -- Both the target level and the level in the given direction are
    -- autoexplored, so we try any unexplored stairs on the target level in
    -- that direction.
    if count_stairs(result.branch, result.depth, dir,
                const.explore.explored)
            < count_stairs(result.branch, result.depth, dir,
                const.explore.reachable) then
        result.stairs_dir = dir
        return true
    end

    -- No unexplored stairs in the given direction on our target level, but on
    -- the level in that direction we have some stairs in the opposite
    -- direction, so we try those.
    if dir_depth_stairs then
        result.depth = dir_depth
        result.stairs_dir = -dir

        finalize_first_dir(result)

        return true
    end

    return false
end

-- Try to get a "final" depth and any needed stair search direction.
function finalize_travel_depth(result)
    if travel_opens_runed_doors(result) then
        result.open_runed_doors = true
        return
    end

    if not autoexplored_level(result.branch, result.depth) then
        return
    end

    -- If we can go up a level within our current branch, finalize depth and
    -- direction in that direction.
    local up_reachable = result.depth > 1
        and count_stairs(result.branch, result.depth, const.dir.up,
            const.explore.reachable) > 0
    local finished
    if up_reachable then
        if finalize_depth_dir(result, const.dir.up) then
            return
        end
    end

    -- If up is not reachable or we didn't finalize in that direction, try to
    -- finalize down.
    local down_reachable = result.depth < branch_depth(result.branch)
        and count_stairs(result.branch, result.depth, const.dir.down,
            const.explore.reachable) > 0
    if down_reachable and finalize_depth_dir(result, const.dir.down) then
        return
    end

    -- We're not successfully finalized, so we'll attempt resets of stair
    -- states for stairs going up and stairs on the level above going down.
    local finished
    if up_reachable
            -- Don't reset up stairs if we still need the branch rune, since we
            -- have specific plans for branch ends we may need to follow.
            and (have_branch_runes(result.branch)
                or result.depth < branch_rune_depth(result.branch)) then
        reset_stone_stairs(result.branch, result.depth, const.dir.up)
        reset_stone_stairs(result.branch, result.depth - 1, const.dir.down)
        result.depth = result.depth - 1
        finalize_first_dir(result)
        result.stairs_dir = const.dir.down
        finished = true
    end

    if down_reachable then
        reset_stone_stairs(result.branch, result.depth, const.dir.down)
        reset_stone_stairs(result.branch, result.depth + 1, const.dir.up)
        -- If we've just reset upstairs, that direction gets priority as the
        -- first search destination.
        if not finished then
            result.depth = result.depth + 1
            finalize_first_dir(result)
            result.stairs_dir = const.dir.up
        end
    end
end

function travel_destination(dest_branch, dest_depth, finalize_dest)
    if not dest_branch or in_portal() then
        return {}
    end

    local result = travel_destination_search(dest_branch, dest_depth)
    -- We were unable enter the branch in result.stop_branch, so figure out the
    -- next best travel location in the branch's parent.
    if result.stop_branch
            and not branch_found(result.stop_branch, const.explore.reachable) then
        local parent, min_depth, max_depth = parent_branch(result.stop_branch)
        result.branch = parent
        result.depth = next_exploration_depth(parent, min_depth, max_depth)
        if not result.depth then
            result.depth = min_depth
        end
    end

    -- Get the final depth to which we should actually travel given the state
    -- of exploration at our travel destination. Some searches never finalize
    -- at their destination because they are for a known objective on the
    -- destination level.
    if finalize_dest
            or result.branch ~= dest_branch
            or result.depth ~= dest_depth then
        finalize_travel_depth(result)
    end

    travel_safe_stairs(result)

    return result
end

function update_goal_travel()
    if goal_status == "Save" or goal_status == "Quit" then
        goal_travel = {}
        return
    end

    -- We use a stash search to reach our destination, but will still do a
    -- travel search for any given goal branch/depth, so we can use a go
    -- command as a backup.
    local want_stash = goal_status == "Orb" and c_persist.found_orb
        or not goal_branch
        or goal_status:find("^God") and goal_branch ~= "Temple"
        or is_portal_branch(goal_branch)
            and not in_portal()
            and branch_found(goal_branch, const.explore.reachable)
        or goal_branch == "Abyss"
            and not in_branch("Abyss")
            and branch_found("Abyss", const.explore.reachable)
        or goal_branch == "Pan"
            and not in_branch("Pan")
            and branch_found("Pan", const.explore.reachable)

    goal_travel = travel_destination(goal_branch, goal_depth,
        not want_stash and goal_status ~= "Escape")

    if goal_status == "Escape" and where == "D:1" then
        goal_travel.first_dir = const.dir.up
    end

    goal_travel.want_stash = want_stash
    goal_travel.want_go = not in_branch("Abyss")
        -- We always try to GD0 when escaping.
        and (goal_status == "Escape"
            or goal_travel.branch
                and (where_branch ~= goal_travel.branch
                    or where_depth ~= goal_travel.depth))

    local goal_reachable = true
    local goal_feats = goal_travel_features()
    local goal_positions
    if goal_feats then
        goal_positions = get_feature_map_positions(goal_feats)
        goal_reachable = false
    end

    if goal_positions then
        for _, pos in ipairs(goal_positions) do
            if map_is_reachable_at(pos) then
                goal_reachable = true
                break
            end
        end
    end

    -- Don't autoexplore if we want to travel in some way. This allows us to
    -- leave the level before it's completely explored.
    disable_autoexplore = (goal_travel.stairs_dir
            or goal_travel.safe_stairs
            or goal_travel.safe_hatch
            or goal_travel.want_go
            or goal_travel.want_stash)
        and goal_reachable
        -- We do allow autoexplore even when we want to travel if the current
        -- is fully explored, since then it's safe to pick up any surrounding
        -- items like thrown projectiles or loot from e.g. stairdancing.
        and (not explored_level(where_branch, where_depth)
        -- However we don't allow autoexplore in this case if we're in the
        -- Abyss, we're escaping with the Orb, or our current level is our
        -- travel destination. The last exception is to allow within-level
        -- plans like taking unexplored stairs and stash searches to on-level
        -- destinations like altars to not be interrupted when runed doors
        -- exist. In that case autoexplore would move us next to a runed door
        -- and off of our intermediate stair, altar, etc., where we need to be.
            or (in_branch("Abyss")
                or goal_status == "Escape" and qw.have_orb
                or goal_travel.branch and not goal_travel.want_go))

    if debug_channel("goals") then
        if goal_travel.branch then
            dsay("Travel destination: "
                .. make_level(goal_travel.branch, goal_travel.depth))
        end

        if goal_travel.stairs_dir then
            dsay("Stairs search dir: " .. tostring(goal_travel.stairs_dir))
        elseif goal_travel.safe_stairs then
            dsay("Taking specific stairs for safety: "
                .. goal_travel.safe_stairs)
        elseif goal_travel.safe_hatch then
            dsay("Taking hatch on destination level for safety at "
                .. pos_string(unhash_position(goal_travel.safe_hatch)))
        end

        if goal_travel.first_dir then
            dsay("First dir: " .. tostring(goal_travel.first_dir))
        elseif goal_travel.first_branch then
            dsay("First branch: " .. tostring(goal_travel.first_branch))
        end

        dsay("Want stash travel: " .. bool_string(goal_travel.want_stash))
        dsay("Want go travel: " .. bool_string(goal_travel.want_go))
        dsay("Disable autoexplore: " .. bool_string(disable_autoexplore))
    end
end

function goal_travel_features()
    local on_travel_level = goal_travel.branch == where_branch
        and goal_travel.depth == where_depth
    if goal_travel.stairs_dir and on_travel_level then
        local feats = level_stairs_features(where_branch, where_depth,
            goal_travel.stairs_dir)
        local wanted_feats = {}
        for _, feat in ipairs(feats) do
            local state = get_stairs(where_branch, where_depth, feat)
            if not state or state.feat < const.explore.explored then
                table.insert(wanted_feats, feat)
            end
        end
        if #wanted_feats > 0 then
            return wanted_feats
        end
    elseif goal_travel.safe_stairs and on_travel_level then
        return { goal_travel.safe_stairs }
    elseif goal_travel.first_dir then
        return level_stairs_features(where_branch, where_depth,
            goal_travel.first_dir)
    elseif goal_travel.first_branch then
        return { branch_entrance(goal_travel.first_branch) }
    elseif on_travel_level then
        local god = goal_god(goal_status)
        if god then
            return { god_altar(god) }
        end
    end
end
---------------------------------------------
-- Per-turn update and other turn-related aspects.

-- A value for sorting last when comparing turns.
const.inf_turns = 200000000

function turn_memo(name, func)
    if qw.turn_memos[name] == nil then
        local val = func()
        if val == nil then
            val = false
        end
        qw.turn_memos[name] = val
    end

    return qw.turn_memos[name]
end

function turn_memo_args(name, func, ...)
    -- Note: crawl uses Lua 5.4 as of DCSS 0.34, so we use select() instead of
    -- the removed Lua 5.1-style implicit arg table.
    local num_args = select('#', ...)
    assert(num_args > 0)

    local parent, key
    for j = 1, num_args do
        if j == 1 then
            parent = qw.turn_memos
            key = name
        end

        if parent[key] == nil then
            parent[key] = {}
        end

        parent = parent[key]

        key = select(j, ...)
        -- We turn any nil argument into false so it can be used as a table
        -- key. This might cause unexpected behaviour for an arbitrary
        -- function.
        if key == nil then
            key = false
        end
    end

    if parent[key] == nil then
        local val = func()
        if val == nil then
            val = false
        end
        parent[key] = val
    end

    return parent[key]
end

function reset_cached_turn_data(force)
    local turns = you.turns()
    if not force and qw.last_turn_reset == turns then
        return
    end

    qw.turn_memos = {}
    qw.best_equip = nil
    qw.attacks = nil
    qw.want_to_kite = nil
    qw.want_to_kite_step = nil

    qw.safe_stairs_failed = false

    qw.last_turn_reset = turns
end

-- We want to call this exactly once each turn.
function turn_update()
    if not qw.initialized then
        initialize()
    end

    local turns = you.turns()
    if turns == qw.turn_count then
        qw.time_passed = false
        return
    end

    qw.have_orb = you.have_orb()
    qw.time_passed = true
    qw.turn_count = turns

    reset_cached_turn_data(true)

    update_equip_tracking()

    if you.turns() >= qw.dump_count then
        dump_count = qw.dump_count + 100
        crawl.dump_char()
    end

    if qw.turn_count >= qw.skill_count then
        qw.skill_count = qw.skill_count + 5
        handle_skills()
    end

    if hp_is_full() then
        qw.full_hp_turn = qw.turn_count
    end

    if you.god() ~= previous_god then
        previous_god = you.god()
        qw.want_goal_update = true
    end

    local new_level = false
    local full_map_clear = false
    if you.where() ~= where then
        new_level = previous_where ~= nil
        cache_parity = 3 - cache_parity

        if you.where() ~= previous_where and new_level then
            full_map_clear = true
        end

        previous_where = where
        where = you.where()
        where_branch = you.branch()
        where_depth = you.depth()
        qw.want_goal_update = true

        qw.can_flee_upstairs = not (in_branch("D") and where_depth == 1
            or in_portal()
            or in_branch("Abyss")
            or in_branch("Pan")
            or in_branch("Tomb") and where_depth > 1
            or in_hell_branch(where_branch))
        qw.base_corrosion = in_branch("Dis") and 8 or 0

        transp_zone = 0
        qw.stuck_turns = 0

        if at_branch_end("Vaults") and not vaults_end_entry_turn then
            vaults_end_entry_turn = qw.turn_count
        elseif where == "Tomb:2" and not tomb2_entry_turn then
            tomb2_entry_turn = qw.turn_count
        elseif where == "Tomb:3" and not tomb3_entry_turn then
            tomb3_entry_turn = qw.turn_count
        end
    end

    if qw.have_orb and where == zot_end then
        qw.ignore_traps = true
    else
        qw.ignore_traps = false
    end

    qw.base_corrosion = qw.base_corrosion
        + 4 * count_adjacent_slimy_walls_at(const.origin)

    if you.flying() then
        gained_permanent_flight = permanent_flight == false
            and not temporary_flight
        if gained_permanent_flight then
            qw.want_goal_update = true
        end

        permanent_flight = not temporary_flight
    else
        permanent_flight = false
        temporary_flight = false
    end

    update_monsters()

    update_map(new_level, full_map_clear)

    qw.position_is_safe = is_safe_at(const.origin)
    qw.position_is_cloudy = not qw.position_is_safe
        and not cloud_is_safe(view.cloud_at(0, 0))

    qw.danger_in_los = #qw.enemy_list > 0
        or not map_is_unexcluded_at(qw.map_pos)
    qw.immediate_danger = check_immediate_danger()

    update_reachable_position()
    update_reachable_features()

    update_move_destination()
    update_flee_positions()

    if qw.want_goal_update then
        update_goal()

        if goal_status == "Save" or goal_status == "Quit" then
            return
        end
    end

    if not c_persist.zig_completed
            and in_branch("Zig")
            and where_depth == goal_zig_depth(goal_status) then
        c_persist.zig_completed = true
    end

    if qw.enemy_memory and qw.enemy_memory_turns_left > 0 then
        qw.enemy_memory_turns_left = qw.enemy_memory_turns_left - 1
    end

    choose_tactical_step()

    map_mode_search_attempts = 0
end
--------------------
-- Utility functions

function enum(tbl)
    local e = {}
    for i = 0, #tbl - 1 do
        e[tbl[i + 1]] = i
    end

    return e
end

function enum_string(val, tbl)
    for k, v in pairs(tbl) do
        if v == val then
            return k
        end
    end
end

function contains_string_in(name, t)
    for _, value in ipairs(t) do
        if name:find(value) then
            return true
        end
    end
    return false
end

function split(str, del)
    local res = {}
    local v
    for v in str:gmatch("([^" .. del .. "]+)") do
        table.insert(res, v)
    end
    return res
end

function bool_string(x)
    return x and "true" or "false"
end

function capitalise(str)
    local lower = str:lower()
    return lower:sub(1, 1):upper() .. lower:sub(2)
end

-- Remove leading and trailing whitespace.
function trim(str)
    -- We do this to avoid returning multiple results from string.gsub().
    local result = str:gsub("^%s+", ""):gsub("%s+$", "")
    return result
end

function sign(a)
    return a > 0 and 1 or a < 0 and -1 or 0
end

function abs(a)
    return a * sign(a)
end

function max(x, y)
    if x > y then
        return x
    else
        return y
    end
end

function min(x, y)
    if x < y then
        return x
    else
        return y
    end
end

function table_is_empty(t)
    local empty = true
    for _, v in pairs(t) do
        empty = false
        break
    end
    return empty
end

function empty_string(s)
    return not s or s == ''
end

--[[
Compare the numeric values of tables for the given keys. The keys are compared
in the order given in `keys`, with the comparison moving to the next key when
there's a tie with the current key.
@table a             A table to compare.
@table b             A table to compare.
@table keys          A list of keys to compare values in tables a and b.
@table reversed_keys A table of keys set to true for a key where the values
                     should be compared in reverse.
@treturn boolean True if a has a key with a higher value (or lower value if the
                 key is reversed) than b, false otherwise.

--]]
function compare_table_keys(a, b, keys, reversed_keys)
    for _, key in ipairs(keys) do
        local val1 = a[key]
        local val2 = b[key]
        local reversed = reversed_keys and reversed_keys[key]
        local greater_val = not reversed and true or false
        if val1 > val2 then
            return greater_val
        elseif val1 < val2 then
            return not greater_val
        end
    end
    return false
end

-----------------------------------------
-- Compatibility helpers for clua API changes in DCSS 0.33 and later.

-- Returns a map of hotkey letters to ability names. This replaces the
-- you.ability_table() function, which was removed in DCSS 0.33, with a
-- construction based on you.ability_info(), whose entries have the format
-- { name, currently_usable, hotkey }.
function ability_table()
    local abil_table = {}
    local abil_info = you.ability_info()
    if abil_info then
        for _, abil in ipairs(abil_info) do
            abil_table[abil[3]] = abil[1]
        end
    end
    return abil_table
end

-- Returns an array of the names of available abilities. This replaces the
-- you.abilities() function, which was removed in DCSS 0.33.
function ability_names()
    local names = {}
    local abil_info = you.ability_info()
    if abil_info then
        for _, abil in ipairs(abil_info) do
            table.insert(names, abil[1])
        end
    end
    return names
end
>
