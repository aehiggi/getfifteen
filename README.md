# getfifteen
## TLA+ spec implementing strategy for the game Get Fifteen

### Overview
From: https://buttondown.email/hillelwayne/archive/nondeterminism-in-formal-specification/

In the game Get Fifteen, players take turns picking numbers 1..9.        
Players can pick each number only once and cannot pick numbers their opponent picked. 
Winner is the first player to have three picked numbers that add to 15. 
This is identical to playing TicTacToe, but is easier to formally specify (no grid)                              
                                                                         
Model a player tictactoe against an AI. Either can start first.
The player needs to follow a deterministic strategy you implement.
The AI just nondeterministically picks any available number.
The property to check is "the player never loses".             

### Implementation

The implementation of player strategy is hard-coded for moves 1 to 4 (implementing tic-tac-toe strategies) then switches to either win or block for subsequent moves.

The AI simply chooses a random card from those remaining at each move.

### Checking the model

Running the model with TLC yields a state space of diameter ranging from 0 to ~50 on each run.

### Checking the model (multiple iterations)

Run the following command to check the model 1000 times, writing the outputs to ``getfifteen.log``.

NOTE: Uses the tla command line tools, installed using https://github.com/pmer/tla-bin

```
rm getfifteen.log; i=0; while (( i < 1000 )); do tlc getfifteen.tla >> getfifteen.log; ((++i)); echo $i; done
```
To verify no violations were found, the following should return no results:
```
grep violate getfifteen.log
```