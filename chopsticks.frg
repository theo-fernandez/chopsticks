#lang forge

option problem_type temporal
option max_tracelength 14

/*---------------*\
|   Definitions   |
\*---------------*/

sig Hand {
    var fingers: lone Int
    // No int --> hand is 'out'
}

sig Team {
	hands : set Hand,
    next : one Team
}

one sig GameState {
    teams : set Team,
    var turn: one Team,
    rollover: one Int,
    even_splits_only: one Int,
    selfAttack: one Int
}

pred selfAttackOk {
    GameState.selfAttack = 1
}

pred selfAttackNotOk {
    GameState.selfAttack = 0
}

pred rolloverOk {
    GameState.rollover = 1
}

pred rolloverNotOk {
    GameState.rollover = 0
}

pred evenSplitsOnly {
    GameState.even_splits_only = 1
}

pred allSplitsValid {
    GameState.even_splits_only = 0
}

pred isRing {
	-- every team gets to go
	Team->Team in ^next
}

pred validState{
    all h: Hand | {
        h.fingers > 0
        h.fingers < 5
    }

    #{GameState.teams} >= 2
}

pred init[numHands: Int]{
    all h: Hand | h.fingers = 1
    all t: Team | #{t.hands} = numHands
    all t: Team | t in GameState.teams

    all h: Hand | one t: Team | {
        h in t.hands
    }
}

pred final {
    some t: Team {
        some h: Hand | {
            h in t.hands implies {
                some h.fingers
            }
        }
        all t2: Team | t != t2 implies {
            all h2: Hand | {
                h2 in t2.hands implies {
                    no h2.fingers
                }
            }
        }
    }
}


pred attack {
    some t: GameState.turn {
        some disj h1, h2: Hand | {
            -- PRE-GUARD: Attacking hand h1 and attacked hand h2
            some h1.fingers and some h2.fingers
            h1 in t.hands 
            {GameState.selfAttack = 0} => h2 not in t.hands

            -- ACTION: Increment h2
            {GameState.rollover = 1} => {
                -- With rollover: Hand dies only at exactly 5, mod 5 otherwise
                add[h2.fingers, h1.fingers] = 5 implies {
                    no h2.fingers'
                } else {
                    h2.fingers' = remainder[add[h2.fingers, h1.fingers], 5]
                }
            } else {
                -- No rollover: Hand dies if more or equal to 5
                add[h2.fingers, h1.fingers] >= 5 implies {
                    no h2.fingers'
                } else {
                    h2.fingers' = add[h2.fingers, h1.fingers]
                }
            }

            -- POST-GUARD: Every hand except h2 is constant
            all h3: Hand | h3 != h2 implies {
                h3.fingers' = h3.fingers
            }
        }
    }
}

pred divide {
    some t: GameState.turn {
        some h1, h2: Hand | {
            h1 in t.hands and some h1.fingers
            h2 in t.hands and no h2.fingers  
            // remainder[num to divide, dividing number]
            GameState.even_splits_only = 1 => {
                remainder[h1.fingers, 2] = 0
            } else {
                remainder[h1.fingers, 2] = 1
            }
            h1.fingers >= 2
            some num: Int {
                num >= 1
                num < h1.fingers
                h2.fingers' = num
                h1.fingers' = subtract[h1.fingers, num]
            }

            all h3: Hand | h3 != h2 and h3 != h1 implies {
                h3.fingers' = h3.fingers
            }
        }
    }
}

pred doNothing {
    final 
    all h: Hand | h.fingers' = h.fingers
    GameState.turn' = GameState.turn
}

pred doMove {
    attack or divide // add divide and transfer
    GameState.turn' = GameState.turn.next
}

pred traces_basic_game {
    init[2]
    rolloverOk
    selfAttackNotOk
    isRing
    noRollover
    evenSplitsOnly
	always (doMove or doNothing)
    // eventually divide // comment this line in if you want the first instance to divide
}

run {
    traces_basic_game
} for exactly 2 Team, 5 Int