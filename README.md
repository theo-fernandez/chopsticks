# 🥢️ Chopsticks

![](https://www.wikihow.com/images/thumb/b/bb/Play-Chopsticks-Step-3-Version-3.jpg/aid144890-v4-728px-Play-Chopsticks-Step-3-Version-3.jpg.webp)

## The Rules
Chopsticks is a game that elementary schoolers play around the world. It is typically a two player game where each player has two hands (though it can be played with more players or more hands). Initially, each player holds up one finger on each hand. On each players turn, they have the opportunity to attack, transfer, or divide. If they attack, they choose one of their hands and an opponents hand and add the number of fingers on their hand to the number of fingers on their opponents hand. If they transfer, they can move fingers from one of their hands to another. Finally, if they can divide, they move fingers from an alive hand to a dead hand. Hands die when the total number of fingers on the hand is five or more. A player loses when they have no hands that are alive. A player wins once all other players have lost. There are many variations on these rules, and we have modelled our favorites.

## Our Representation
Our representation uses temporal forge to model the hands changing across moves. We use a `Hand` sig to model how many fingers each `Hand` has. If a player's `Hand` "dies," then the `Hand` has zero fingers. Each `Hand` is then assigned to a `Team` sig. A `Team` can represent one player (1-2 hands) or more (3+ hands). `Hand`s are placed in a set so that we can have a variable number of hands depending on the rules that we are using for the specific game. We have `Rule` sigs, which keep track of specific rules that we are using for the current game. Finally, we have a `Game` sig. `Game` keeps track of which team's turn it is, as well as what rules are being used in the `Game`.

Originally, instead of pointing to `one Int`, `Hand` pointed to a `lone Int`. When a hand was alive, it would point to an `Int` representing the number of fingers it has. When it died, it didn't point to anything. However, when implementing our `transfer` pred, we decided that it was easier to always have the `Hand` pointing to an `Int`.

Originally, `Team` did not have a `transferStreak` field. However, in order to make sure that hands did not transfer finger back and forth forever, we added this field to make the game more interesting.

Finally, `Game` originally pointed to all of the `Team`s in the game. This relation was not useful to modeling the game so we removed it. The `rules` field was added in after we started to allow us to easily change the rules in our traces. We added in the `lastChangedH1` and `lastChangedH2` fields to help with the visualization later.

## Scope of the Model
Forge struggles to handle bigger traces, and our model is no exception. Our model is designed to be extensible so that it can handle any valid number of teams and hands. However, due to Forge's limited ability to find satisfiable solutions, our model struggles to model more than two teams and four hands (though it is able to). 

For our model to work correctly, we need to be able to add two integers together to get eight. By default, Forge integers range from -8 to 7. In order to make our model work correctly, we need to expand the integer range to -16 to 15, even though we only use integers ranging from 0 to 8. Using so many integers most likely slows Forge down when trying to find possible solutions. To overcome this challenge, we account for overflow in addition and use 4 `Int`, even though it makes our model slightly less understandable.

Beyond the time limitations, our model is able to find possible game traces for the most common versions of chopsticks. If the model could be run more quickly, the scope of our model would be greatly expanded.

A possible limitation of our model is the addition of new rules. Each predicate needs to be updated individually when rules are added using implication. We could hypothetically change our structure to use sub-predicates to better accomodate new rules.

Testing in temporal Forge occassionally proved to be difficult. If we wanted to check that something would be true in the fifth state, we had to chain five `next_state`s together. We were able to do this, but it would have been convenient to be able to specify a specific state in temporal Forge. While it didn't 

## Modification of Goals
Our goals stayed mostly consistent throughout the project. Although we designed our model initially to work with two or more players, it initially always returned `unsat` when we tried to run it with three players. We struggled to figure out what might be causing this issue, especially because all of our logic seemed correct. We considered dropping three player functionality for this reason.

However, after a lot of testing, we discovered that having more than 4 `Hand` sigs caused the model to return `unsat` every time. When we added `for 6 Hand` to the end of the run and testing statements, the model worked for 3 `Team`. This issue was annoying to debug, but we are glad we were able to keep 3 `Team` in the scope.

## Understanding the Custom Visualizer
An instance of our model should be understood as a full game of the game Chopsticks. Each state in temporal Forge is one state in the game. A move is taken between each state.

The custom visualizer shows each state of the game. Each team is a row, and every column (excluding the first) is the number of fingers in that hand. If it is a team's turn, the box with their team name is highlighted in light gray. 

On every turn in the game, a hand takes an action and another hand is the recipient of the action. The hand taking the action is highlighted in light red and the hand recieving the action is highlighted in light blue. For example, if the previous action was an attack, the hand that attacked will be red and the hand that was attacked will be blue. In the case of division, the hand dividing is red and the hand being given fingers is blue.

## What our Model Proved
As a kid, Theo wondered whether these games would go on forever. Now, he feels vindicated. It is possible for almost every variation of the game to go on indefinitely.

Using the `Suicide` ruleset, the game is able to end one move more quickly than it would be able to without using the `Suicide` rules.

Our model proved Wikipedia wrong. Using the official rules of the game, wikipedia lists possible hand states that should not be reachable. However, our model showed that some of these unreachable states are in fact reachable when a player attacks themselves. 

We also proved the maximum game length where no game states are repeated on Wikipedia wrong. Wikipedia says the maximum number of moves should be 9 for no revisitation, but we found a trace length with 10 moves.

## General Observations
Temporal Forge could be difficult to use when trying to find a specific state. For example, we wanted to check that in each board state, that specific board state had never existed before. Without using partial functions, checking that a board state has not existed before seems to be impossible.