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
    next_state next_state next_state next_state next_state doNothing
}

pred nineMoveMax{
    // "The longest possible game that gets farther[clarification needed] from the starting point with each move is 9 moves."
    {next_state next_state next_state next_state next_state next_state next_state next_state not gameEnded
    and eventually doNothing} => 
    {next_state next_state next_state next_state next_state next_state next_state next_state next_state gameEnded}
}

pred twelveMoveMax{
    // "The longest possible game that gets farther[clarification needed] from the starting point with each move is 9 moves."
    {next_state next_state next_state next_state next_state next_state next_state next_state next_state not gameEnded
    and eventually doNothing} => 
    {next_state next_state next_state next_state next_state next_state next_state next_state next_state next_state gameEnded}
}


pred onlySelfAttackReachableState {
    some disj h1, h2, h3, h4: Hand, g: Game, t2: Team{
        t2 != g.turn
        h1 in g.turn.hands and h2 in g.turn.hands
        h3 in t2.hands and h4 in t2.hands

        fingers = h1->1 + h2->1 + h3->0 + h4->1 or
        fingers = h1->2 + h2->2 + h3->0 + h4->2 or
        fingers = h1->3 + h2->3 + h3->0 + h4->3 or 
        fingers = h1->4 + h2->4 + h3->0 + h4->4
    }
}

pred unreachableState {
    some disj h1, h2, h3, h4: Hand, g: Game, t2: Team{
        t2 != g.turn
        h1 in g.turn.hands and h2 in g.turn.hands
        h3 in t2.hands and h4 in t2.hands

        fingers = h1->0 + h2->0 + h3->0 + h4->0 or
        fingers = h1->0 + h2->1 + h3->0 + h4->0 or
        fingers = h1->0 + h2->2 + h3->0 + h4->0 or
        fingers = h1->0 + h2->3 + h3->0 + h4->0 or
        fingers = h1->0 + h2->4 + h3->0 + h4->0 or
        fingers = h1->1 + h2->1 + h3->0 + h4->0 or
        fingers = h1->1 + h2->2 + h3->0 + h4->0 or
        fingers = h1->1 + h2->3 + h3->0 + h4->0 or
        fingers = h1->1 + h2->4 + h3->0 + h4->0 or
        fingers = h1->1 + h2->4 + h3->0 + h4->0 or
        fingers = h1->2 + h2->2 + h3->0 + h4->0 or
        fingers = h1->2 + h2->3 + h3->0 + h4->0 or
        fingers = h1->2 + h2->4 + h3->0 + h4->0 or
        fingers = h1->3 + h2->3 + h3->0 + h4->0 or
        fingers = h1->2 + h2->4 + h3->0 + h4->0 or
        fingers = h1->3 + h2->4 + h3->4 + h4->4 or
        fingers = h1->4 + h2->4 + h3->0 + h4->0 or
        fingers = h1->4 + h2->4 + h3->4 + h4->4
    }
}

pred bothPlayersHaveOneHand {
    some disj t1, t2: Team {
        some h1, h2: Hand{
            h1 in t1.hands and h2 in t2.hands
            fingers = h1->0 + h2->0
        }
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
        // Can find nine-move (Wikipedia wrong)
        nineMoveMaxOfficialRules :{
            not {tracesOfficialRules[2] implies nineMoveMax}
            } for exactly 2 Team, 4 Int, 6 Hand is sat

        // Can find twelve-move
        twelveMoveMaxTracesOfficial :{
            not{tracesOfficialRules[2] implies twelveMoveMax}
        } for exactly 2 Team, 4 Int, 4 Hand is sat


        vacuityTracesOfficial: {
            tracesOfficialRules[2]
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canEndTracesOfficial: {
            tracesOfficialRules[2] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canLoopForeverTracesOfficial: {
            tracesOfficialRules[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        impossiblyShortTracesOfficial: {
            tracesOfficialRules[2] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        shortestGameTracesOfficial: {
            tracesOfficialRules[2] implies shortestGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        // Takes a really long time to check
        // invalidHandsTracesOfficial: {
        //     tracesOfficialRules[2] and eventually unreachableState
        // } for exactly 2 Team, 4 Int, 4 Hand is unsat

        selfAttackExclusiveTracesOfficial: {
            tracesOfficialRules[2] and eventually onlySelfAttackReachableState
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        eventuallyBothPlayersPlayOneHandedTracesOfficial: {
            tracesOfficialRules[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        playerWinsWithOneFingerEachHandTracesOfficial: {
            tracesOfficialRules[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 4 Int, 4 Hand is sat
    }

    -- Official Rules but Each Player has 3 Hands
    test expect {
        vacuityTracesOfficial: {
            tracesOfficialRules[3]
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        canEndTracesOfficial: {
            tracesOfficialRules[3] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        canLoopForeverTracesOfficial: {
            tracesOfficialRules[3] implies not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        impossiblyShortTracesOfficial: {
            tracesOfficialRules[3] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 6 Hand is unsat

        alwaysValidTracesOfficial: {
            tracesOfficialRules[3] implies always validState
        } for exactly 2 Team, 4 Int, 6 Hand is sat
    }
}

test suite for tracesOnlyGetsFarther {
    test expect {
        // Wikipedia is wrong!! Finds a 10-move trace
        nineMoveMaxOfficialRules :{
            not{tracesOnlyGetsFarther[2] implies nineMoveMax}
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        // Can play up to twelve
        twelveMoveMaxTracesFarther :{
            not{tracesOnlyGetsFarther[2] implies twelveMoveMax}
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        vacuityTracesFurther: {
            tracesOnlyGetsFarther[2]
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canEndTracesFurther: {
            tracesOnlyGetsFarther[2] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canLoopForeverTracesFurther: {
            tracesOnlyGetsFarther[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        impossiblyShortTracesFurther: {
            tracesOnlyGetsFarther[2] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        shortestGameTracesFurther: {
            tracesOnlyGetsFarther[2] implies shortestGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is sat
        
        
        // Takes a really long time to check
        // invalidHands: {
        //     tracesGetsFurther[2] and eventually unreachableState
        // } for exactly 2 Team, 4 Int, 4 Hand is unsat

        selfAttackExclusiveTracesFurther: {
            tracesOnlyGetsFarther[2] and eventually onlySelfAttackReachableState
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        alwaysValidTracesFurther: {
            tracesOnlyGetsFarther[2] implies always validState
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        eventuallyBothPlayersPlayOneHandedTracesFurther: {
            tracesOnlyGetsFarther[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        playerWinsWithOneFingerEachHandTracesFurthere: {
            tracesOnlyGetsFarther[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 4 Int, 4 Hand is sat
    }
}

test suite for tracesSuicide {
    test expect {
        vacuityTracesSuicide: {
            tracesSuicide[2]
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        canEndTracesSuicide: {
            tracesSuicide[2] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        canLoopForeverTracesSuicide: {
            tracesSuicide[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        // This is only sat for this ruleset
        impossiblyShortTracesSuicide: {
            tracesSuicide[2] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        shortestGameTracesSuicide: {
            tracesSuicide[2] implies shortestGameLength
        } for exactly 2 Team, 4 Int, 6 Hand is sat
        
        // Takes a really long time to check
        // invalidHands: {
        //     tracesSuicide[2] and eventually unreachableState
        // } for exactly 2 Team, 4 Int, 6 Hand is unsat

        selfAttackExclusiveTracesSuicide: {
            tracesOfficialRules[2] and eventually onlySelfAttackReachableState
        } for exactly 2 Team, 4 Int, 4 Hand is sat


        alwaysValidTracesSuicide: {
            tracesSuicide[2] implies always validState
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHandedTracesSuicide: {
            tracesSuicide[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHandTracesSuicide: {
            tracesSuicide[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 4 Int, 6 Hand is sat
    }
}

test suite for tracesCutoff {
    test expect {
        vacuityTracesCutoff: {
            tracesCutoff[2]
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canEndTracesCutoff: {
            tracesCutoff[2] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canLoopForeverTracesCutoff: {
            tracesCutoff[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        impossiblyShortTracesCutoff: {
            tracesCutoff[2] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        shortestGameTracesCutoff: {
            tracesCutoff[2] implies shortestGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is sat
        
        // Takes a really long time to check
        // invalidHands: {
        //     tracesCutoff[2] and eventually unreachableState
        // } for exactly 2 Team, 4 Int, 4 Hand is unsat

        selfAttackExclusiveTracesCutoff: {
            tracesOfficialRules[2] and eventually onlySelfAttackReachableState
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        alwaysValidTracesCutoff: {
            tracesCutoff[2] implies always validState
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        eventuallyBothPlayersPlayOneHandedTracesCutoff: {
            tracesCutoff[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        playerWinsWithOneFingerEachHandTracesCutoff: {
            tracesCutoff[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 4 Int, 4 Hand is sat
    }
}

test suite for tracesTransfersOnly {
    test expect {
        vacuityTracesTransferOnly: {
            tracesTransfersOnly[2]
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canEndTracesTransferOnly: {
            tracesTransfersOnly[2] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canLoopForeverTracesTransferOnly: {
            tracesTransfersOnly[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        impossiblyShortTracesTransferOnly: {
            tracesTransfersOnly[2] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        shortestGameTracesTransferOnly: {
            tracesTransfersOnly[2] implies shortestGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        // Takes a really long time to check
        // invalidHands: {
        //     tracesTransfersOnly[2] and eventually unreachableState
        // } for exactly 2 Team, 4 Int, 4 Hand is unsat

        selfAttackExclusiveTracesTransferOnly: {
            tracesOfficialRules[2] and eventually onlySelfAttackReachableState
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        alwaysValidTracesTransferOnly: {
            tracesTransfersOnly[2] implies always validState
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        eventuallyBothPlayersPlayOneHandedTracesTransferOnly: {
            tracesTransfersOnly[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        playerWinsWithOneFingerEachHandTracesTransferOnly: {
            tracesTransfersOnly[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 4 Int, 4 Hand is sat
    }
}

test suite for tracesDivisionsOnly {
    test expect {
        vacuityTracesDivisionsOnly: {
            tracesDivisionsOnly[2]
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canEndTracesDivisionsOnly: {
            tracesDivisionsOnly[2] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canLoopForeverTracesDivisionsOnly: {
            tracesDivisionsOnly[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        impossiblyShortTracesDivisionsOnly: {
            tracesDivisionsOnly[2] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        shortestGameTracesDivisionsOnly: {
            tracesDivisionsOnly[2] implies shortestGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is sat
        
        // Takes a really long time to check
        // invalidHandsTracesDivisionsOnly: {
        //     tracesDivisionsOnly[2] and eventually unreachableState
        // } for exactly 2 Team, 4 Int, 4 Hand is unsat

        selfAttackExclusiveTracesDivisionsOnly: {
            tracesOfficialRules[2] and eventually onlySelfAttackReachableState
        } for exactly 2 Team, 4 Int, 4 Hand is sat
        alwaysValid: {
            tracesDivisionsOnly[2] implies always validState
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        eventuallyBothPlayersPlayOneHandedTracesDivisionsOnly: {
            tracesDivisionsOnly[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 4 Int, 4 Hand is sat
        

        playerWinsWithOneFingerEachHandTracesDivisionsOnly: {
            tracesDivisionsOnly[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 4 Int, 4 Hand is sat
    }
}

test suite for tracesLCWRules {
    test expect {
        vacuityTracesLCW: {
            tracesLCWRules[2]
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canEndTracesLCW: {
            tracesLCWRules[2] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        canLoopForeverTracesLCW: {
            tracesLCWRules[2] implies not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        impossiblyShortTracesLCW: {
            tracesLCWRules[2] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        shortestGameTracesLCW: {
            tracesLCWRules[2] implies shortestGameLength
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        selfAttackExclusiveTracesLCW: {
            tracesLCWRules[2] and eventually onlySelfAttackReachableState
        } for exactly 2 Team, 4 Int, 4 Hand is unsat

        // Takes a really long time to check
        // invalidHands: {
        //     tracesLCWRules[2] and eventually unreachableState
        // } for exactly 2 Team, 4 Int, 4 Hand is unsat

        alwaysValidTracesLCW: {
            tracesLCWRules[2] implies always validState
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        eventuallyBothPlayersPlayOneHandedTracesLCW: {
            tracesLCWRules[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 4 Int, 4 Hand is sat

        playerWinsWithOneFingerEachHandTracesLCW: {
            tracesLCWRules[2] implies eventually playerWinsUnscathed
        } for exactly 2 Team, 4 Int, 4 Hand is sat
    }
}

test suite for tracesDeathmatch {
    test expect {
        // Finds a 11-move trace
        nineMoveMaxOfficialRules :{
            not {tracesDeathmatch[2] implies nineMoveMax}
        } for exactly 2 Team, 4 Int, 4 Hand is sat
        vacuityTracesDM: {
            tracesDeathmatch[2]
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        canEndTracesDM: {
            tracesDeathmatch[2] implies eventually gameEnded
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        canLoopForeverTracesDM: {
            tracesDeathmatch[2] and not (eventually gameEnded)
        } for exactly 2 Team, 4 Int, 6 Hand is unsat

        impossiblyShortTracesDM: {
            tracesDeathmatch[2] and impossiblyShortGameLength
        } for exactly 2 Team, 4 Int, 6 Hand is unsat

        shortestGameTracesDM: {
            tracesDeathmatch[2] implies shortestGameLength
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        invalidHandsTracesDM: {
            tracesDeathmatch[2] and eventually unreachableState
        } for exactly 2 Team, 4 Int, 6 Hand is unsat

        alwaysValidTracesDM: {
            tracesDeathmatch[2] implies always validState
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHandedTracesDM: {
            tracesDeathmatch[2] implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 4 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHandTracesDM: {
            tracesDeathmatch[2] and eventually playerWinsUnscathed
        } for exactly 2 Team, 4 Int, 6 Hand is unsat

        // -- Deathmatch played with three teams (instead of two)
        vacuityThreeTeamsTracesDM: {
            tracesDeathmatch[2]
        } for exactly 3 Team, 4 Int, 6 Hand is sat

        canEndThreeTeamsTracesDM: {
            tracesDeathmatch[2] implies eventually gameEnded
        } for exactly 3 Team, 4 Int, 6 Hand is sat

        canLoopForeverThreeTeamsTracesDM: {
            tracesDeathmatch[2] and not (eventually gameEnded)
        } for exactly 3 Team, 4 Int, 6 Hand is unsat

        impossiblyShortThreeTeamsTracesDM: {
            tracesDeathmatch[2] and impossiblyShortGameLength
        } for exactly 3 Team, 4 Int, 6 Hand is unsat

        shortestGameThreeTeamsTracesDM: {
            tracesDeathmatch[2] implies shortestGameLength
        } for exactly 3 Team, 4 Int, 6 Hand is sat

        alwaysValidTracesDM: {
            tracesDeathmatch[2] implies always validState
        } for exactly 3 Team, 4 Int, 6 Hand is sat
    }
}
