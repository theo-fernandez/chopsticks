# Chopsticks Game

## The Rules
Chopsticks is a game that elementary schoolers play around the world. It is typically a two player game where each player has two hands (though it can be played with more players or more hands). Initially, each player holds up one finger on each hand. On each players turn, they have the opportunity to attack, transfer, or divide. If they attack, they choose one of their hands and an opponents hand and add the number of fingers on their hand to the number of fingers on their opponents hand. If they transfer, they can move fingers from one of their hands to another. Finally, if they can divide, they move fingers from an alive hand to a dead hand. Hands die when the total number of fingers on the hand is five or more. A player loses when they have no hands that are alive. A player wins once all other players have lost. There are many variations on these rules, and we have modelled our favorites.

## Our Representation
Our representation uses temporal forge to model the hands changing across moves. We use a hand sig to model how many fingers each hand has. If a player's hand "dies," then the hand has zero fingers. Each hand is then assigned to a team sig. A team can represent one player (1-2 hands) or more (3+ hands). Hands are placed in a set so that we can have a variable number of hands depending on the rules that we are using.

## Scope of the Model

## Modification of Goals

## Understanding the Custom Visualizer