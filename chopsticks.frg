#lang forge

option problem_type temporal
option max_tracelength 14

/*---------------*\
|   Definitions   |
\*---------------*/

sig Hand {
    fingers: lone Int
    // No int --> hand is 'out'
}

sig Team {
	var hands : set Hand
}

pred init[numHands: Int]{
    all h: Hand | h.fingers = 1
    all t: Team | #{t.hands} = numHands
}

pred validState{
    all h: Hand | {
        h.fingers > 0
        h.fingers < 5
    }
}

pred final{
    some t: Team | {
        all h: Hand | {
            h in t.hands => no h.fingers
        }
    }
}