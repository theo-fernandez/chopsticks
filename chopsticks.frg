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
    var turn: one Team
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
        some h1, h2: Hand | {
            h1 in t.hands and some h1.fingers
            h2 not in t.hands and some h2.fingers  

            add[h2.fingers, h1.fingers] >= 5 implies {
                no h2.fingers'
            } else {
                h2.fingers' = add[h2.fingers, h1.fingers]
            }

            all h3: Hand | h3 != h2 implies {
                h3.fingers' = h3.fingers
            }
        }
    }
}

pred doNothing{
    final 
    all h: Hand | h.fingers' = h.fingers
    GameState.turn' = GameState.turn
}

pred doMove {
    attack // add divide and transfer
    GameState.turn' = GameState.turn.next
}

pred traces_basic_game {
    init[2]
    isRing
	always (doMove or doNothing)
}

run {
    traces_basic_game
} for exactly 2 Team, 5 Int