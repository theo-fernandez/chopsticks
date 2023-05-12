#lang forge

open "chopsticks.frg"

/*--------------------------*\
|   Model-Checking Tests     |
\*--------------------------*/
test suite for init {
    test expect {
        correctInit: {
            some disj t1, t2: Team, h1, h2: Hand {
                t1 != t2 and h1 != h2
                next = t1 -> t2 + t2 -> t1
                fingers = h1 -> 1 + h2 -> 1
                turn = Game-> t1
                hands = t1 -> h1 + t2 -> h2
            }
            init[1]
        } is sat

        sharedHandInit: {
            some disj t1, t2: Team, h1: Hand {
                t1 != t2 
                next = t1 -> t2 + t2 -> t1
                fingers = h1 -> 1
                turn = Game-> t1
                hands = t1 -> h1 + t2 -> h1
            }
            init[1]
        } is unsat

        oddHandsInit: {
            #{Hand} = 3
            #{Team} = 2
            init[2]
        } is unsat
    }
}

test suite for attack {
    test expect {
        attackTwoTeamsTwoHands: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->1 + h2->1 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->1 + h2->1 + h3->2 + h4->1

                attack
            }
        } is sat

        attackTwoTeamsTwoHandsRollover: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand, r: Rollover{
                next = t1->t2 + t2->t1
                isRing
                rules = Game->r

                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->4 + h2->1 + h3->1 + h4->4

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->4 + h2->1 + h3->1 + h4->3 // Rolled over on h4

                attack
            }
        } for 4 Int is sat


        attackTwoTeamsTwoHandsFail: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->1 + h2->1 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->1 + h2->1 + h3->1

                attack
            }
        } is unsat

        attackTwoTeamsSelfAttackWithRule: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand, s: SelfAttack {
                next = t1->t2 + t2->t1
                isRing

                rules = Game->s
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->1 + h2->1 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->1 + h2->2 + h3->1 + h4->1

                attack
            }
        } is sat

        attackTwoTeamsSelfAttackWithoutRule: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->1 + h2->1 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->1 + h2->2 + h3->1 + h4->1

                attack
            }
        } is unsat
        
        attackTwoTeamsEliminatesHand: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->2 + h2->1 + h3->1 + h4->3

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->2 + h2->1 + h3->1 + h4->0

                attack
            }
        } is sat

        attackTwoTeamsOneValidMove: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->2 + h2->2 + h3->1 + h4->0

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->2 + h2->2 + h3->3 + h4->0

                attack
            }
        } is sat

        // attackThreePlayers: {
        //     some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
        //         next = t1->t2 + t2->t3 + t3 -> t1
        //         isRing
        //         hands = t1->h1 + t1->h2 + t2->h3 + t2->h4 + t3 -> h5 + t3-> h6

        //         -- State 0
        //         transferStreak = t1->0 + t2->0 + t3->0
        //         turn = Game->t1
        //         fingers = h1->1 + h2->1 + h3->1 + h4->1 + h5->1 + h6->1

        //         -- State 1
        //         transferStreak' = t1->0 + t2->0 + t3->0
        //         turn' = Game->t2
        //         fingers' = h1->1 + h2->1 + h3->2 + h4->1 + h5->1 + h6->1

        //         attack
        //     }
        // } is sat
    }
}

test suite for transfer {
    // Check if rollover should be tested here too
    test expect {
        transferTwoTeamsTwoHands: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->4 + h2->1 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->1 + t2->0
                turn' = Game->t2
                fingers' = h1->3 + h2->2 + h3->1 + h4->1

                transfer[3]
            }
        } is sat

        transferTwoTeamsTwoHandsLessThanTransferStreak: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->4 + h2->1 + h3->2 + h4->1

                -- State 1
                transferStreak' = t1->1 + t2->0
                turn' = Game->t2
                fingers' = h1->3 + h2->2 + h3->2 + h4->1

                -- State 2
                transferStreak'' = t1->1 + t2->1
                turn'' = Game->t1
                fingers'' = h1->3 + h2->2 + h3->1 + h4->2

                -- State 3
                transferStreak''' = t1->2 + t2->0
                turn''' = Game->t2
                fingers''' = h1->1 + h2->4 + h3->2 + h4->1

                transfer[2]
                next_state transfer[2]
                // next_state next_state transfer[2]
            }
        } is sat

        transferTwoTeamsTwoHandsMoreThanTransferStreak: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->4 + h2->1 + h3->2 + h4->1

                -- State 1
                transferStreak' = t1->1 + t2->0
                turn' = Game->t2
                fingers' = h1->3 + h2->2 + h3->2 + h4->1

                -- State 2
                transferStreak'' = t1->1 + t2->1
                turn'' = Game->t1
                fingers'' = h1->3 + h2->2 + h3->1 + h4->2

                -- State 1
                transferStreak''' = t1->2 + t2->0
                turn''' = Game->t2
                fingers''' = h1->1 + h2->4 + h3->2 + h4->1

                transfer[1]
                next_state transfer[1]
                next_state next_state transfer[1]
            }
        } is unsat

        transferTwoTeamsTwoHandsSuicideAllowed: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand, suicide: Suicide {
                next = t1->t2 + t2->t1
                isRing

                rules = Game->suicide
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->2 + h2->1 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->1 + t2->0
                turn' = Game->t2
                fingers' = h1->0 + h2->3 + h3->1 + h4->1

                transfer[3]
            }
        } is sat

        transferTwoTeamsTwoHandsTrySuicide: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->2 + h2->1 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->1 + t2->0
                turn' = Game->t2
                fingers' = h1->0 + h2->3 + h3->1 + h4->1

                transfer[3]
            }
        } is unsat

        transferTwoTeamsTwoHandsSuicideRolloverAllowed: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand, suicide: Suicide, rollover: Rollover {
                next = t1->t2 + t2->t1
                isRing

                rules = Game->suicide + Game->Rollover
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->3 + h2->3 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->1 + t2->0
                turn' = Game->t2
                fingers' = h1->0 + h2->1 + h3->1 + h4->1

                transfer[3]
            }
        } is sat

        transferTwoTeamsTwoHandsRolloverAllowed: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand, rollover: Rollover {
                next = t1->t2 + t2->t1
                isRing

                rules = Game->Rollover
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->4 + h2->4 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->1 + t2->0
                turn' = Game->t2
                fingers' = h1->1 + h2->2 + h3->1 + h4->1

                transfer[3]
            }
        } is sat

        transferTwoTeamsTwoHandsRolloverAllowedTrySuicide: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand, rollover: Rollover {
                next = t1->t2 + t2->t1
                isRing

                rules = Game->Rollover
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->2 + h2->4 + h3->1 + h4->1

                -- State 1
                transferStreak' = t1->1 + t2->0
                turn' = Game->t2
                fingers' = h1->0 + h2->1 + h3->1 + h4->1

                transfer[3]
            }
        } is unsat

        transferTwoTeamsTwoHandsNotOnTurn: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->2 + h2->1 + h3->4 + h4->1

                -- State 1
                transferStreak' = t1->1 + t2->0
                turn' = Game->t2
                fingers' = h1->2 + h2->1 + h3->3 + h4->2

                transfer[3]
            }
        } is unsat
    }
}

test suite for divide {
    test expect {
        divideTwoTeamsTwoHandsEven: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t2
                fingers = h1->3 + h2->0 + h3->0 + h4->2

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t1
                fingers' = h1->3 + h2->0 + h3->1 + h4->1

                divide
            }
        } is sat

        divideTwoTeamsTwoHandsOdd: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->3 + h2->0 + h3->0 + h4->2

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->2 + h2->1 + h3->0 + h4->2

                divide
            }
        } is sat

        // TODO figure out why it doesn't work with disj
        divideTwoTeamsTwoHandsEvensOnlySuccess: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand, eo: EvenSplitsOnly {
                next = t1->t2 + t2->t1
                isRing

                rules = Game->eo
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t2
                fingers = h1->3 + h2->0 + h3->0 + h4->2

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t1
                fingers' = h1->3 + h2->0 + h3->1 + h4->1

                divide
            }
        } is sat

        divideTwoTeamsTwoHandsEvensOnlyFail: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand, eo: EvenSplitsOnly {
                next = t1->t2 + t2->t1
                isRing

                rules = Game->eo
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->3 + h2->0 + h3->0 + h4->2

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->2 + h2->1 + h3->0 + h4->2

                divide
            }
        } is unsat

        divideTwoTeamsTwoHandsNotOnTurn: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand, eo: EvenSplitsOnly {
                t1 != t2
                next = t1->t2 + t2->t1
                isRing

                rules = Game->eo
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->3 + h2->0 + h3->0 + h4->2

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->3 + h2->0 + h3->1 + h4->1

                divide
            }
        } is unsat
    }
}

test suite for pass {
    test expect {
        passGood: {
            some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
                next = t1->t2 + t2->t3 + t3->t1
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4 + t3->h5 + t3->h6

                -- State 0
                turn = Game->t1
                fingers = h1->0 + h2->0 + h3->1 + h4->1 + h5->1 + h6->1

                -- State 1
                turn' = Game->t2
                fingers' = h1->0 + h2->0 + h3->1 + h4->1 + h5->1 + h6->1
                
                pass
            }
        } for 6 Hand, 3 Team is sat

        passNever2P :{
            init[2]
            some disj t1, t2: Team {
                isRing
            }
                            
            always {attack or pass or doNothing}
            eventually pass
        } is unsat

        passNever2PVacuity :{
            init[2]
            some disj t1, t2: Team {
                isRing
            }
                            
            always {attack or pass or doNothing}
        } is sat

        passEndgame: {
            some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
                next = t1->t2 + t2->t3 + t3->t1
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4 + t3->h5 + t3->h6

                -- State 0
                turn = Game->t1
                fingers = h1->0 + h2->0 + h3->0 + h4->0 + h5->1 + h6->1

                -- State 1
                turn' = Game->t2
                fingers' = h1->0 + h2->0 + h3->0 + h4->0 + h5->1 + h6->1
                
                pass
            }
        } is unsat
        
        passChangedFingers: {
            some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
                next = t1->t2 + t2->t3 + t3->t1
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4 + t3->h5 + t3->h6

                -- State 0
                turn = Game->t1
                fingers = h1->0 + h2->0 + h3->1 + h4->1 + h5->1 + h6->1

                -- State 1
                turn' = Game->t2
                fingers' = h1->0 + h2->0 + h3->2 + h4->1 + h5->1 + h6->1 // h3 changed fingers
                
                pass
            }
        } is unsat
        
        passStillHaveFingers: {
            some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
                next = t1->t2 + t2->t3 + t3->t1
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4 + t3->h5 + t3->h6

                -- State 0
                turn = Game->t1
                fingers = h1->1 + h2->0 + h3->1 + h4->1 + h5->1 + h6->1 // h1 still has fingers

                -- State 1
                turn' = Game->t2
                fingers' = h1->1 + h2->0 + h3->1 + h4->1 + h5->1 + h6->1 
                
                pass
            }
        } is unsat
    }
}

test suite for gameEnded {
    test expect {
        gameEndedTwoPlayersWinnersTurn: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 1
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->3 + h2->0 + h3->0 + h4->0

                gameEnded
            }
        } is sat

        gameEndedTwoPlayersLosersTurn: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 1
                transferStreak = t1->0 + t2->0
                turn = Game->t2
                fingers = h1->3 + h2->0 + h3->0 + h4->0

                gameEnded
            }
        } is sat

        gameNotEndedTwoPlayers: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t2
                fingers = h1->3 + h2->0 + h3->1 + h4->0

                gameEnded
            }
        } is unsat

        // gameEndedThreePlayersWinnersTurn: {
        //     some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
        //         next = t1->t2 + t2->t3 + t3 -> t1
        //         isRing

        //         no rules
        //         hands = t1->h1 + t1->h2 + 
        //                 t2->h3 + t2->h4 + 
        //                 t3 -> h5 + t3-> h6

        //         -- State 0
        //         transferStreak = t1->0 + t2->0 + t3->0
        //         turn = Game->t1
        //         fingers = h1->3 + h2->0 + h3->0 + h4->0 + h5->0 + h6->0

        //         gameEnded
        //     }
        // } is sat
    }
}

test suite for doNothing {
    test expect {
        doNothingTwoPlayers: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->3 + h2->0 + h3->0 + h4->0

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t1
                fingers' = h1->3 + h2->0 + h3->0 + h4->0

                doNothing
            }
        } is sat

        doNothingTwoPlayersTurnChanges: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->3 + h2->0 + h3->0 + h4->0

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t2
                fingers' = h1->3 + h2->0 + h3->0 + h4->0

                doNothing
            }
        } is unsat

        doNothingTwoPlayersFingersChange: {
            some disj t1, t2: Team, h1, h2, h3, h4: Hand {
                next = t1->t2 + t2->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4

                -- State 0
                transferStreak = t1->0 + t2->0
                turn = Game->t1
                fingers = h1->3 + h2->0 + h3->0 + h4->0

                -- State 1
                transferStreak' = t1->0 + t2->0
                turn' = Game->t1
                fingers' = h1->2 + h2->1 + h3->0 + h4->0

                doNothing
            }
        } is unsat

        doNothingThreePlayers: {
            some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
                next = t1->t2 + t2->t3 + t3 -> t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + 
                        t2->h3 + t2->h4 + 
                        t3 -> h5 + t3-> h6

                -- State 0
                transferStreak = t1->0 + t2->0 + t3->0
                turn = Game->t1
                fingers = h1->3 + h2->0 + h3->0 + h4->0 + h5->0 + h6->0

                -- State 1
                transferStreak' = t1->0 + t2->0 + t3->0
                turn' = Game->t1
                fingers' = h1->3 + h2->0 + h3->0 + h4->0 + h5->0 + h6->0

                doNothing
            }
        } for 6 Hand is sat

        doNothingThreePlayersNotWinnersTurn: {
            some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
                next = t1->t2 + t2->t3 + t3->t1
                isRing

                no rules
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4 + t3->h5 + t3->h6

                -- State 0
                transferStreak = t1->0 + t2->0 + t3->0
                turn = Game->t2
                fingers = h1->3 + h2->0 + h3->0 + h4->0 + h5->0 + h6->0

                -- State 1
                transferStreak' = t1->0 + t2->0 + t3->0
                turn' = Game->t2
                fingers' = h1->3 + h2->0 + h3->0 + h4->0 + h5->0 + h6->0

                doNothing
            }
        } for 6 Hand is sat
    }
}

/*--------------------------*\
|   Investigative predicates  |
\*--------------------------*/

pred impossiblyShortGameLength {
    next_state next_state next_state next_state doNothing
}

pred shortestGameLength {
    // Wikipedia: "Shortest possible game is 5 moves"
    next_state next_state next_state next_state next_state doNothing
}

pred unreachableState {
    some disj h1, h2, h3, h4: Hand, g: Game, t2: Team{
        t2 != g.turn
        h1 in g.turn.hands and h2 in g.turn.hands
        h3 in t2.hands and h4 in t2.hands

        fingers = h1->4 + h2->4 + h3->4 + h4->4 or 
        fingers = h1->0 + h2->0 + h3->0 + h4->0
    }
}

pred bothPlayersHaveOneHand {
    some disj t1, t2: Team, h1: t1.hands, h2: t2.hands {
        fingers = h1->0 + h2->0
    }
}

pred playerWinsUnscathed {
    gameEnded
    some disj h1, h2: Hand {
        fingers = h1->1 + h2->1
    }
}

pred validState {
    all h: Hand | {
        h.fingers >= 0
        h.fingers < 5
    }

    #{Team} >= 2
}

/*--------------------------*\
|   Investigative tests      |
\*--------------------------*/
test suite for tracesOfficialRules {
    test expect {
        vacuity: {
            tracesOfficialRules[2]
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canEnd: {
            tracesOfficialRules[2] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canLoopForever: {
            tracesOfficialRules[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        impossiblyShort: {
            tracesOfficialRules[2] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        shortestGame: {
            tracesOfficialRules[2] implies shortestGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        invalidHands: {
            tracesOfficialRules[2] and eventually unreachableState
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        eventuallyBothPlayersPlayOneHanded: {
            tracesOfficialRules[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesOfficialRules[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 4 Int, 4 Hand is sat
    }

    -- Official Rules but Each Player has 3 Hands
    test expect {
        vacuity: {
            tracesOfficialRules[3]
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesOfficialRules[3] implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesOfficialRules[3] implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesOfficialRules[3] and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesOfficialRules[3] implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesSuicide {
    test expect {
        vacuity: {
            tracesSuicide[2]
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesSuicide[2] implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesSuicide[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesSuicide[2] and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesSuicide[2] implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesSuicide[2] and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesSuicide[2] implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesSuicide[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesSuicide[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesCutoff {
    test expect {
        vacuity: {
            tracesCutoff[2]
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesCutoff[2] implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesCutoff[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesCutoff[2] and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesCutoff[2] implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesCutoff[2] and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesCutoff[2] implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesCutoff[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesCutoff[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesTransfersOnly {
    test expect {
        vacuity: {
            tracesTransfersOnly[2]
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesTransfersOnly[2] implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesTransfersOnly[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesTransfersOnly[2] and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesTransfersOnly[2] implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesTransfersOnly[2] and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesTransfersOnly[2] implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesTransfersOnly[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesTransfersOnly[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesDivisionsOnly {
    test expect {
        vacuity: {
            tracesDivisionsOnly[2]
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesDivisionsOnly[2] implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesDivisionsOnly[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesDivisionsOnly[2] and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesDivisionsOnly[2] implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesDivisionsOnly[2] and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesDivisionsOnly[2] implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesDivisionsOnly[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesDivisionsOnly[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesLCWRules {
    test expect {
        vacuity: {
            tracesLCWRules[2]
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesLCWRules[2] implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesLCWRules[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesLCWRules[2] and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesLCWRules[2] implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesLCWRules[2] and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesLCWRules[2] implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesLCWRules[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesLCWRules[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

// test suite for tracesDeathmatch {
//     test expect {
//         vacuity: {
//             tracesDeathmatch[2]
//         } for exactly 2 Team, 5 Int, 6 Hand is sat

//         canEnd: {
//             tracesDeathmatch[2] implies eventually gameEnded
//         } for exactly 2 Team, 5 Int, 6 Hand is sat

//         canLoopForever: {
//             tracesDeathmatch[2] and not (eventually gameEnded)
//         } for exactly 2 Team, 5 Int, 6 Hand is unsat

//         impossiblyShort: {
//             tracesDeathmatch[2] and impossiblyShortGameLength
//         } for exactly 2 Team, 5 Int, 6 Hand is unsat

//         shortestGame: {
//             tracesDeathmatch[2] implies shortestGameLength
//         } for exactly 2 Team, 5 Int, 6 Hand is sat

//         invalidHands: {
//             tracesDeathmatch[2] and eventually unreachableState
//         } for exactly 2 Team, 5 Int, 6 Hand is unsat

//         alwaysValid: {
//             tracesDeathmatch[2] implies always validState
//         } for exactly 2 Team, 5 Int, 6 Hand is sat

//         eventuallyBothPlayersPlayOneHanded: {
//             tracesDeathmatch[2] implies eventually always bothPlayersHaveOneHand
//         } for exactly 2 Team, 5 Int, 6 Hand is sat

//         playerWinsWithOneFingerEachHand: {
//             tracesDeathmatch[2] and eventually playerWinsUnscathed
//         } for exactly 2 Team, 5 Int, 6 Hand is unsat

//         // -- Deathmatch played with three teams (instead of two)
//         vacuityThreeTeams: {
//             tracesDeathmatch[2]
//         } for exactly 3 Team, 5 Int, 6 Hand is sat

//         canEndThreeTeams: {
//             tracesDeathmatch[2] implies eventually gameEnded
//         } for exactly 3 Team, 5 Int, 6 Hand is sat

//         canLoopForeverThreeTeams: {
//             tracesDeathmatch[2] and not (eventually gameEnded)
//         } for exactly 3 Team, 5 Int, 6 Hand is unsat

//         impossiblyShortThreeTeams: {
//             tracesDeathmatch[2] and impossiblyShortGameLength
//         } for exactly 3 Team, 5 Int, 6 Hand is unsat

//         shortestGameThreeTeams: {
//             tracesDeathmatch[2] implies shortestGameLength
//         } for exactly 3 Team, 5 Int, 6 Hand is sat

//         alwaysValid: {
//             tracesDeathmatch[2] implies always validState
//         } for exactly 3 Team, 5 Int, 6 Hand is sat
//     }
// }
