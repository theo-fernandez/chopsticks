#lang forge

option problem_type temporal
option max_tracelength 20

/*---------------*\
|   Definitions   |
\*---------------*/

sig Hand {
    var fingers: one Int
    // 0 --> hand is 'out'
}

sig Team {
	hands : set Hand,
    next : one Team,
    var transferStreak: lone Int
}

abstract sig Rule {}

one sig Rollover extends Rule {}
one sig EvenSplitsOnly extends Rule {}
one sig SelfAttack extends Rule {}
one sig Suicide extends Rule {}

one sig Game {
    teams : set Team,
    var turn: one Team,
    rules: set Rule
}

/*--------------------*\
|   Rule Predicates   |
\*--------------------*/
pred selfAttackOk {
    SelfAttack in Game.rules
}

pred selfAttackNotOk {
    SelfAttack not in Game.rules
}

pred rolloverOk {
    Rollover in Game.rules
}

pred rolloverNotOk {
    Rollover not in Game.rules
}

pred suicideOk {
    Suicide in Game.rules
}

pred suicideNotOk {
    Suicide not in Game.rules
}

pred evenSplitsOnly {
    EvenSplitsOnly in Game.rules
}

pred allSplitsValid {
    EvenSplitsOnly not in Game.rules
}

pred isRing {
	-- Every team gets to go
	Team->Team in ^next
}

// pred validState{
//     all h: Hand | {
//         h.fingers >= 0
//         h.fingers < 5
//     }

//     #{Game.teams} >= 2
// }

pred init[numHands: Int]{
    isRing

    all h: Hand | h.fingers = 1
    all t: Team | {
        #{t.hands} = numHands
        t.transferStreak = 0
    }

    all h: Hand | one t: Team | {
        h in t.hands
    }
}

pred gameEnded {
    some t: Team {
        some h: Hand | {
            h in t.hands implies {
                h.fingers > 0
            }
        }
        all t2: Team | t != t2 implies {
            all h2: Hand | {
                h2 in t2.hands implies {
                    h2.fingers = 0
                }
            }
        }
    }
}

/*---------*\
|   Moves  |
\*---------*/

pred attack {
    some t: Game.turn {
        some disj h1, h2: Hand | {
            -- PRE-GUARD: Attacking hand h1, attacked hand h2
            h1.fingers > 0 and h2.fingers > 0
            h1 in t.hands 
            {SelfAttack not in Game.rules} => h2 not in t.hands

            -- ACTION: Increment h2
            {Rollover in Game.rules} => {
                -- With rollover: Hand dies only at exactly 5, mod 5 otherwise
                add[h2.fingers, h1.fingers] = 5 implies {
                    h2.fingers' = 0
                } else {
                    h2.fingers' = remainder[add[h2.fingers, h1.fingers], 5]
                }
            } else {
                -- No rollover: Hand dies if more or equal to 5
                add[h2.fingers, h1.fingers] >= 5 implies {
                    h2.fingers' = 0
                } else {
                    h2.fingers' = add[h2.fingers, h1.fingers]
                }
            }
            -- ACTION: Change Turn
            Game.turn' = Game.turn.next

            -- POST-GUARD: Every hand except h2 is constant
            all h3: Hand | h3 != h2 implies {
                h3.fingers' = h3.fingers
            }
            
        }

        t.transferStreak' = 0
        all t2: Team | t2 != t implies {
            t2.transferStreak' = t2.transferStreak
        }
    }
}

pred transfer[maxStreak: Int] {
    some t: Game.turn {
        -- PRE-GUARD: Player has not transfered more than thrice in a row
        t.transferStreak < maxStreak
    
        some disj h1, h2: Hand {
            -- PRE-GUARD: h1 and h2 belong to the same player and neither are dead
            h1 in t.hands and h1.fingers > 0
            h2 in t.hands and h2.fingers > 0

            -- ACTION: Finger count changes but total fingers stay the same
            h1.fingers' != h1.fingers
            h2.fingers' != h2.fingers
            add[h1.fingers', h2.fingers'] = add[h1.fingers, h2.fingers]

            // -- No adding more than five to one hand
            // Could also be in a valid state predicate instead?
            h1.fingers' < 5 and h1.fingers' >=0
            h2.fingers' < 5 and h2.fingers' >= 0

            -- ACTION: Change Turn
            Game.turn' = Game.turn.next

            -- POST-GUARD: Every hand except h2/h1 is constant
            all h3: Hand | h3 != h2 and h3 != h1 implies {
                h3.fingers' = h3.fingers
            }
        }
        t.transferStreak' = add[t.transferStreak, 1]
        all t2: Team | t2 != t implies {
            t2.transferStreak' = t2.transferStreak
        }

    }
    
}
pred divide {
    some t: Game.turn {
        some h1, h2: Hand {
            -- PRE-GUARD: Attacking hand h1 and attacked hand h2
            h1 in t.hands and h1.fingers > 0
            h2 in t.hands and h2.fingers = 0
            EvenSplitsOnly in Game.rules => {
                remainder[h1.fingers, 2] = 0
            } else {
                remainder[h1.fingers, 2] = 1
            }

            -- ACTION: Decrement h1 and increment h2
            some num: Int {
                num >= 1
                {Suicide in Game.rules} implies {
                    num <= h1.fingers
                } else {
                    num < h1.fingers
                }
                h2.fingers' = num
                h1.fingers' = subtract[h1.fingers, num]
            }
            -- ACTION: Change Turn
            Game.turn' = Game.turn.next

            -- POST-GUARD: Every hand except h2, h1 is constant
            all h3: Hand | h3 != h2 and h3 != h1 implies {
                h3.fingers' = h3.fingers
            }
        }
        t.transferStreak' = 0
        all t2: Team | t2 != t implies {
            t2.transferStreak' = t2.transferStreak
        }
    }
}

pred pass {
    some t: Game.turn {
        all h: Hand {
            -- PRE-GUARD: Hands have no fingers
            h in t.hands implies {
                h.fingers = 0
            }
        
            -- ACTION: Change Turn
            Game.turn' = Game.turn.next
        }
    }
}

pred doNothing {
    gameEnded
    all h: Hand | h.fingers' = h.fingers
    Game.turn' = Game.turn
}

/*---------------*\
|   Rule traces  |
\*---------------*/

pred traces_official_rules {
    init[2]

    rolloverOk
    selfAttackOk
    allSplitsValid
    suicideNotOk

    always (attack or divide or transfer[3] or doNothing)
    eventually always doNothing
}

pred traces_official_rules_threehands {
    init[3]

    rolloverNotOk
    selfAttackOk
    allSplitsValid
    suicideNotOk

    always (attack or divide or transfer[3] or doNothing)
    // eventually always doNothing
}


// pred traces_misere {
//     // We need to change the win condition for this to work
// }

// pred traces_suicide {
//     init[2]
//     isRing

//     rolloverOk
//     selfAttackOk
//     allSplitsValid
//     suicideOk

//     always (attack or divide or transfer[3] or doNothing)
// }

// pred traces_swaps {}
// pred traces_sudden_death {}
// pred traces_meta {}
// pred traces_logan_clause {}

// pred traces_cutoff {
//     init[2]
//     isRing

//     rolloverNotOk
//     selfAttackOk
//     allSplitsValid
//     suicideNotOk

//     always (attack or divide or transfer[3] or doNothing)
// }

// pred traces_zombies {}

// pred traces_transfers_only {
//     init[2]
//     isRing

//     rolloverNotOk
//     selfAttackOk
//     allSplitsValid
//     suicideNotOk

//     always (attack or transfer[3] or doNothing)
// }

// pred traces_divisions_only {
//     init[2]
//     isRing

//     rolloverNotOk
//     selfAttackOk
//     allSplitsValid
//     suicideNotOk

//     always (attack or divide or doNothing)
// }

pred traces_theo_rules {
    init[2]

    rolloverNotOk
    selfAttackNotOk
    evenSplitsOnly
    suicideNotOk

    always (attack or divide or pass or doNothing)
}

run {
    traces_theo_rules
} for exactly 3 Team, 5 Int