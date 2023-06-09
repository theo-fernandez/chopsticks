#lang forge

option problem_type temporal
option max_tracelength 15
option min_tracelength 5
option solver Glucose

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
    rules: set Rule,

    // For visualization
    var turn: one Team,
    var lastChangedH1: lone Hand,
    var lastChangedH2: lone Hand
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
    
    no lastChangedH1
    no lastChangedH2
    // #{Game.lastChanged} = 0
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

// For operability with 4 Int --> corrects -1 to what it should be for 8
fun rollover[num1, num2: Int]: Int { {add[num1, num2] < 0} => 3 else remainder[add[num1, num2], 5]}
fun isAboveFive[number: Int]: Int {{number > 5} or {number < 0}}

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
                    // h2.fingers' = remainder[add[h2.fingers, h1.fingers], 5]
                    h2.fingers' = rollover[h1.fingers, h2.fingers]
                }
            } else {
                -- No rollover: Hand dies if more or equal to 5
                {isAboveFive[add[h2.fingers, h1.fingers]] or 
                    add[h2.fingers, h1.fingers] = 5} implies {
                    h2.fingers' = 0
                } else {
                    h2.fingers' = add[h2.fingers, h1.fingers]
                }
            }
            -- ACTION: Change Turn
            Game.turn' = Game.turn.next

            -- Update last changed
            Game.lastChangedH1' = h1
            Game.lastChangedH2' = h2
            

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

            -- ACTION: Finger count changes
            h1.fingers' != h1.fingers
            h2.fingers' != h2.fingers
            h1.fingers' < 5 and h2.fingers' < 5

            -- ACTION: Pick a number, remove it from one hand, and add it to the other.
            -- Modifies the number picked based on the Suicide and Rollover rules.
            some num: Int {
                num >= 1

                {Suicide in Game.rules} implies {
                    num <= h1.fingers
                } else {
                    num < h1.fingers
                }

                {Rollover in Game.rules} implies {
                    {Suicide not in Game.rules} implies {
                        // remainder[add[num, h2.fingers], 5] != 0
                        rollover[num, h2.fingers] != 0
                    }

                    // h2.fingers' = remainder[add[num, h2.fingers], 5]
                    h2.fingers' = rollover[num, h2.fingers]
                    h1.fingers' = subtract[h1.fingers, num]
                } else {
                    {Suicide not in Game.rules} implies {
                        not isAboveFive[h2.fingers + num]
                    }

                    {isAboveFive[add[num, h2.fingers]]} implies {
                        h2.fingers' = 0
                    } else {
                        h2.fingers' = add[num, h2.fingers]
                    }

                    h1.fingers' = subtract[h1.fingers, num]
                }
            }

            -- ACTION: Change Turn
            Game.turn' = Game.turn.next
            -- Update last changed
            Game.lastChangedH1' = h1
            Game.lastChangedH2' = h2

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
            h1 in t.hands and h1.fingers > 1
            h2 in t.hands and h2.fingers = 0
            EvenSplitsOnly in Game.rules => {
                remainder[h1.fingers, 2] = 0
            }

            -- ACTION: Decrement h1 and increment h2
            some num: Int {
                num >= 1
                num < h1.fingers
                h2.fingers' = num
                h1.fingers' = subtract[h1.fingers, num]
            }
            -- ACTION: Change Turn
            Game.turn' = Game.turn.next
            -- Update last changed
            Game.lastChangedH1' = h1
            Game.lastChangedH2' = h2

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
    not gameEnded
    some t: Game.turn {
        all h: Hand {
            -- PRE-GUARD: Hands have no fingers
            h in t.hands implies h.fingers = 0

            -- ACTION: Change Turn
            Game.turn' = Game.turn.next
            -- Update last changed
            no lastChangedH1'
            no lastChangedH2'
        
            -- POST-GUARD: Every hand is constant
            h.fingers' = h.fingers
        }
        -- POST-GUARD: Every transferstreak is constant
        all t2: Team | {
            t2.transferStreak' = t2.transferStreak
        }
    }
}

pred doNothing {
    gameEnded
    all h: Hand | h.fingers' = h.fingers

    Game.turn' = Game.turn
    no lastChangedH1'
    no lastChangedH2'
    // #{Game.lastChanged'} = 0
}

/*---------------*\
|   Rule traces  |
\*---------------*/

pred tracesOfficialRules[handsPerPlayer: Int] {
    init[handsPerPlayer]

    rolloverOk
    selfAttackOk
    allSplitsValid
    suicideNotOk

    always (attack or divide or transfer[3] or pass or doNothing)
}

pred tracesSuicide[handsPerPlayer: Int] {
    init[handsPerPlayer]
    isRing

    rolloverOk
    selfAttackOk
    allSplitsValid
    suicideOk

    always (attack or divide or transfer[3] or pass or doNothing)
}

pred tracesCutoff[handsPerPlayer: Int] {
    init[handsPerPlayer]
    isRing

    rolloverNotOk
    selfAttackOk
    allSplitsValid
    suicideNotOk

    always (attack or divide or transfer[3] or pass or doNothing)
}

pred tracesTransfersOnly[handsPerPlayer: Int] {
    init[handsPerPlayer]
    isRing

    rolloverNotOk
    selfAttackOk
    allSplitsValid
    suicideNotOk

    always (attack or transfer[3] or pass or doNothing)
}

pred tracesDivisionsOnly[handsPerPlayer: Int] {
    init[handsPerPlayer]
    isRing

    rolloverNotOk
    selfAttackOk
    allSplitsValid
    suicideNotOk

    always (attack or divide or pass or doNothing)
}

pred tracesLCWRules[handsPerPlayer: Int] {
    init[handsPerPlayer]

    rolloverNotOk
    selfAttackNotOk
    evenSplitsOnly
    suicideNotOk

    always (attack or divide or pass or doNothing)
}

pred tracesDeathmatch[handsPerPlayer: Int] {
    init[handsPerPlayer]
    isRing

    rolloverNotOk
    selfAttackOk
    suicideNotOk

    always (attack or pass or doNothing)
}

pred tracesOnlyGetsFarther[handsPerPlayer: Int] {
    init[handsPerPlayer]
    isRing

    rolloverOk
    selfAttackNotOk
    suicideNotOk

    always (attack or pass or doNothing)
}



// run {
//     tracesSuicide[2]
//     next_state next_state next_state next_state doNothing
// } for exactly 2 Team, 4 Int, 6 Hand

// run {
//     tracesOfficialRules[2]
//     eventually divide
//     eventually doNothing
// } for exactly 2 Team, 4 Int, 6 Hand

// run {
//     tracesOfficialRules[2]
//     eventually divide
//     eventually doNothing
// } for exactly 2 Team, 4 Int, 6 Hand

// run {
//     tracesLCWRules[2]
//     next_state next_state next_state next_state next_state gameEnded
// } for exactly 2 Team, 4 Int, 6 Hand

run {
    tracesOfficialRules[3]
    // eventually doNothing
} for exactly 3 Team, 4 Int, 9 Hand