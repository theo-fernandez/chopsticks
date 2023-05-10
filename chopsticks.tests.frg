#lang forge

open "chopsticks.frg"

test suite for full_game_three_players {
    test expect {
//         playersTurnNoFingers: {
            // some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
            //     next = t1->t2 + t2->t3 + t3 -> t1
            //     isRing
            //     no rules
            //     hands = t1->h1 + t1->h2 + 
            //             t2->h3 + t2->h4 + 
            //             t3 -> h5 + t3-> h6
            //     teams = Game->t1 + Game->t2 + Game->t3

//                 // transferStreak = t1->0 + t2->0 + t3->0
//                 // turn = Game->t1
//                 // fingers = h1->2 + h2->4 + h3->2 + h4->0 + h5->0 + h6->3

//                 // -- State 8
//                 transferStreak' = t1->0 + t2->0 + t3->0
//                 turn' = Game->t2
//                 fingers' = h1->2 + h2->4 + h3->2 + h4->0 + h5->0 + h6->0

//                 // -- State 9
//                 transferStreak'' = t1->0 + t2->0 + t3->0
//                 turn'' = Game->t3
//                 fingers'' = h1->4 + h2->4 + h3->2 + h4->0 + h5->0 + h6->0
//             }
//             attack
//             next_state attack
//         } is sat

        // middleGameThreePlayers: {
        //     some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
        //         next = t1->t2 + t2->t3 + t3 -> t1
        //         isRing
        //         no rules
        //         hands = t1->h1 + t1->h2 + 
        //                 t2->h3 + t2->h4 + 
        //                 t3 -> h5 + t3-> h6
        //         teams = Game->t1 + Game->t2 + Game->t3

        //         -- State 7
        //         transferStreak = t1->0 + t2->0 + t3->0
        //         turn = Game->t1
        //         fingers = h1->2 + h2->4 + h3->2 + h4->0 + h5->0 + h6->1

        //         -- State 8
        //         transferStreak' = t1->0 + t2->0 + t3->0
        //         turn' = Game->t2
        //         fingers' = h1->2 + h2->4 + h3->2 + h4->0 + h5->0 + h6->0

        //         // -- State 9
        //         transferStreak'' = t1->0 + t2->0 + t3->0
        //         turn'' = Game->t3
        //         fingers'' = h1->4 + h2->4 + h3->2 + h4->0 + h5->0 + h6->0
        //     }
        //         attack
        //         // next_state attack
        //         // next_state pass
        // } is sat
    }
}


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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
        //         teams = Game->t1 + Game->t2 + Game->t3

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
        //         teams = Game->t1 + Game->t2 + Game->t3

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
                teams = Game -> t1 + Game -> t2
                isRing
            }
                            
            always {attack or pass or doNothing}
            eventually pass
        } is unsat

        passNever2PVacuity :{
            init[2]
            some disj t1, t2: Team {
                teams = Game -> t1 + Game -> t2
                isRing
            }
                            
            always {attack or pass or doNothing}
        } is sat

        passEndgame: {
            some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
                next = t1->t2 + t2->t3 + t3->t1
                hands = t1->h1 + t1->h2 + t2->h3 + t2->h4 + t3->h5 + t3->h6
                teams = Game->t1 + Game->t2 + Game->t3

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
                teams = Game->t1 + Game->t2 + Game->t3

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
                teams = Game->t1 + Game->t2 + Game->t3

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
        //         teams = Game->t1 + Game->t2 + Game->t3

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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
                teams = Game->t1 + Game->t2

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

        // doNothingThreePlayers: {
        //     some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
        //         next = t1->t2 + t2->t3 + t3 -> t1
        //         isRing

        //         no rules
        //         hands = t1->h1 + t1->h2 + 
        //                 t2->h3 + t2->h4 + 
        //                 t3 -> h5 + t3-> h6
        //         teams = Game->t1 + Game->t2 + Game->t3

        //         -- State 0
        //         transferStreak = t1->0 + t2->0 + t3->0
        //         turn = Game->t1
        //         fingers = h1->3 + h2->0 + h3->0 + h4->0 + h5->0 + h6->0

        //         -- State 1
        //         transferStreak' = t1->0 + t2->0 + t3->0
        //         turn' = Game->t1
        //         fingers' = h1->3 + h2->0 + h3->0 + h4->0 + h5->0 + h6->0

        //         doNothing
        //     }
        // } is sat

        // doNothingThreePlayersNotWinnersTurn: {
        //     some disj t1, t2, t3: Team, h1, h2, h3, h4, h5, h6: Hand {
        //         next = t1->t2 + t2->t3 + t3->t1
        //         isRing

        //         no rules
        //         hands = t1->h1 + t1->h2 + t2->h3 + t2->h4 + t3->h5 + t3->h6
        //         teams = Game->t1 + Game->t2 + Game->t3

        //         -- State 0
        //         transferStreak = t1->0 + t2->0 + t3->0
        //         turn = Game->t2
        //         fingers = h1->3 + h2->0 + h3->0 + h4->0 + h5->0 + h6->0

        //         -- State 1
        //         transferStreak' = t1->0 + t2->0 + t3->0
        //         turn' = Game->t2
        //         fingers' = h1->3 + h2->0 + h3->0 + h4->0 + h5->0 + h6->0

        //         doNothing
        //     }
        // } is sat
    }
}

// test suite for traces_vacuity {
//     test expect {
//         vacuity_official_rules: {
//             traces_official_rules
//         } for 5 Int is sat

//         vacuity_official_rules_three_hands: {
//             traces_official_rules_three_hands
//         } for 5 Int is sat

//         vacuity_suicide: {
//             traces_suicide
//         } for 5 Int is sat

//         vacuity_cutoff: {
//             traces_cutoff
//         } for 5 Int is sat

//         vacuity_transfers_only: {
//             traces_transfers_only
//         } for 5 Int is sat

//         vacuity_divisions_only: {
//             traces_divisions_only
//         } for 5 Int is sat

//         vacuity_LCW_rules: {
//             traces_LCW_rules
//         } for 5 Int is sat

//         // vacuity_LCW_rules_3_teams: {
//         //     traces_LCW_rules
//         // } for exactly 3 Team, 5 Int is sat
//     }
// }

// test suite for traces_all_games_can_end {
//     test expect {
//         official_rules_can_end: {
//             traces_official_rules implies eventually gameEnded
//         } for 5 Int is sat

//         official_rules_three_hands_can_end: {
//             traces_official_rules_three_hands implies eventually gameEnded
//         } for 5 Int is sat

//         suicide_can_end: {
//             traces_suicide implies eventually gameEnded
//         } for 5 Int is sat

//         cutoff_can_end: {
//             traces_cutoff implies eventually gameEnded
//         } for 5 Int is sat

//         transfers_only_can_end: {
//             traces_transfers_only implies eventually gameEnded
//         } for 5 Int is sat

//         divisions_only_can_end: {
//             traces_divisions_only implies eventually gameEnded
//         } for 5 Int is sat

//         LCW_rules_can_end: {
//             traces_LCW_rules implies eventually gameEnded
//         } for 5 Int is sat
//     }
// }
