#lang forge

open "chopsticks.frg"


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
        // TODO doesn't work with disj
        // passGood: {
        //     some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
        //         next = t1->t2 + t2->t3 + t3->t1
        //         hands = t1->h1 + t1->h2 + t2->h3 + t2->h4 + t3->h5 + t3->h6

        //         -- State 0
        //         turn = Game->t1
        //         fingers = h1->0 + h2->0 + h3->1 + h4->1 + h5->1 + h6->1

        //         -- State 1
        //         turn' = Game->t2
        //         fingers' = h1->0 + h2->0 + h3->1 + h4->1 + h5->1 + h6->1
                
        //         pass
        //     }
        // } is sat

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

/*------------------------*\
|   Investigative traces  |
\*------------------------*/

pred impossiblyShortGameLength {
    next_state next_state next_state next_state doNothing
}

pred shortestGameLength {
    // Wikipedia: "Shortest possible game is 5 moves"
    next_state next_state next_state next_state next_state doNothing
}

pred unreachableState {
    some disj h1, h2, h3, h4: Hand {
        fingers = h1->4 + h2->4 + h3->4 + h4->4
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

test suite for tracesOfficialRules {
    test expect {
        vacuity: {
            tracesOfficialRules
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesOfficialRules implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesOfficialRules implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesOfficialRules and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesOfficialRules implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesOfficialRules and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        eventuallyBothPlayersPlayOneHanded: {
            tracesOfficialRules implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesOfficialRules implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesOfficialRulesThreeHands {
    test expect {
        vacuity: {
            tracesOfficialRulesThreeHands
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesOfficialRulesThreeHands implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesOfficialRulesThreeHands implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesOfficialRulesThreeHands and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesOfficialRulesThreeHands implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesSuicide {
    test expect {
        vacuity: {
            tracesSuicide
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesSuicide implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesSuicide implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesSuicide and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesSuicide implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesSuicide and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesSuicide implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesSuicide implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesSuicide implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesCutoff {
    test expect {
        vacuity: {
            tracesCutoff
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesCutoff implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesCutoff implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesCutoff and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesCutoff implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesCutoff and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesCutoff implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesCutoff implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesCutoff implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesTransfersOnly {
    test expect {
        vacuity: {
            tracesTransfersOnly
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesTransfersOnly implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesTransfersOnly implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesTransfersOnly and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesTransfersOnly implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesTransfersOnly and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesTransfersOnly implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesTransfersOnly implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesTransfersOnly implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesDivisionsOnly {
    test expect {
        vacuity: {
            tracesDivisionsOnly
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesDivisionsOnly implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesDivisionsOnly implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesDivisionsOnly and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesDivisionsOnly implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesDivisionsOnly and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesDivisionsOnly implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesDivisionsOnly implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesDivisionsOnly implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesLCWRules {
    test expect {
        vacuity: {
            tracesLCWRules
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesLCWRules implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesLCWRules implies not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        impossiblyShort: {
            tracesLCWRules and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesLCWRules implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesLCWRules and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesLCWRules implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesLCWRules implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesLCWRules implies eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is sat
    }
}

test suite for tracesDeathmatch {
    test expect {
        vacuity: {
            tracesDeathmatch
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canEnd: {
            tracesDeathmatch implies eventually gameEnded
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        canLoopForever: {
            tracesDeathmatch and not (eventually gameEnded)
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        impossiblyShort: {
            tracesDeathmatch and impossiblyShortGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        shortestGame: {
            tracesDeathmatch implies shortestGameLength
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        invalidHands: {
            tracesDeathmatch and eventually unreachableState
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        alwaysValid: {
            tracesDeathmatch implies always validState
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        eventuallyBothPlayersPlayOneHanded: {
            tracesDeathmatch implies eventually always bothPlayersHaveOneHand
        } for exactly 2 Team, 5 Int, 6 Hand is sat

        playerWinsWithOneFingerEachHand: {
            tracesDeathmatch and eventually playerWinsUnscathed
        } for exactly 2 Team, 5 Int, 6 Hand is unsat

        // -- Deathmatch played with three teams (instead of two)
        vacuityThreeTeams: {
            tracesDeathmatch
        } for exactly 3 Team, 5 Int, 6 Hand is sat

        canEndThreeTeams: {
            tracesDeathmatch implies eventually gameEnded
        } for exactly 3 Team, 5 Int, 6 Hand is sat

        canLoopForeverThreeTeams: {
            tracesDeathmatch and not (eventually gameEnded)
        } for exactly 3 Team, 5 Int, 6 Hand is unsat

        impossiblyShortThreeTeams: {
            tracesDeathmatch and impossiblyShortGameLength
        } for exactly 3 Team, 5 Int, 6 Hand is unsat

        shortestGameThreeTeams: {
            tracesDeathmatch implies shortestGameLength
        } for exactly 3 Team, 5 Int, 6 Hand is sat

        alwaysValid: {
            tracesDeathmatch implies always validState
        } for exactly 3 Team, 5 Int, 6 Hand is sat
    }
}
