------------------------------ MODULE getfifteen ---------------------------- 
(***************************************************************************)
(*In the game Get Fifteen, players take turns picking numbers 1..9.        *)
(*Players can pick each number only once and cannot pick numbers their     *)
(*opponent picked.                                                         *)
(*Winner is the first player to have three picked numbers that add to 15.  *)
(*This is identical to playing TicTacToe,                                  *)
(*but is easier to formally specify (no grid)                              *)
(*                                                                         *)
(*Model a player tictactoe against an AI. Either can start first.          *)
(*The player needs to follow a deterministic strategy you implement.       *)
(*The AI just nondeterministically picks any available number.             *)
(*The property to check is "the player never loses".                       *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, Sequences, Randomization

CONSTANT winningSets, corners, centre, edges

VARIABLES player,   \* The set of cards the human currently has.
          ai,  \* The set of cards the ai currently has.
          remainingCards, \* the set of cards remaining.
          playing, \* who is taking a card
          nextRandom \* random remaining card value to pass to next step

vars == <<remainingCards, player, ai, playing, nextRandom>>

TypeOK == IsFiniteSet(ai) /\ IsFiniteSet(player)

NoOverlaps == (\A c \in player: c \notin ai) 
                /\ (\A c \in ai: c \notin player)
                /\ (\A c \in ai: c \notin remainingCards)
                /\ (\A c \in ai: c \notin remainingCards)

MaxInSet(set) ==
    CHOOSE num \in set: ~(\E n \in set : n > num)

PlayerWinningSetsInPlay == { s \in winningSets: Cardinality(s \ ai) = 3 }

PlayerWinningCards ==
    { c \in remainingCards: 
        \E s \in PlayerWinningSetsInPlay: 
            Cardinality((s \ player) \ {c}) = 0 }

AiWinningSetsInPlay == { s \in winningSets: Cardinality(s \ player) = 3 }

AiWinningCards ==
    { c \in remainingCards: 
        \E s \in AiWinningSetsInPlay: 
            Cardinality((s \ ai) \ {c}) = 0 }

AiPartialWinningSets ==
    { s \in AiWinningSetsInPlay: Cardinality(s \ ai) < 3 }
        
PlayerUsefulCards ==
    \* remaining cards that belong one of our potential winning sets
    (remainingCards \intersect UNION PlayerWinningSetsInPlay) \ player

PlayerUsefulCardsPower == 
    \* the number of winning sets each useful card appears in (more sets = more power)
    { << c, Cardinality({ s \in PlayerWinningSetsInPlay: c \in s}) >> 
        :c \in PlayerUsefulCards }
PlayerMaxPower == MaxInSet({ c[2]: c \in PlayerUsefulCardsPower })

AiUsefulCards ==
    (remainingCards \intersect (UNION AiWinningSetsInPlay)) \ ai

AiUsefulCardsPower == 
    { << c, Cardinality({ s \in AiPartialWinningSets: c \in s}) >> 
        :c \in AiUsefulCards }

BlockingCards == (remainingCards \intersect (UNION AiPartialWinningSets)) \ ai
CalcBlockingPower(partial, useful) ==
    { << c, Cardinality({ s \in partial: Cardinality((s \ ai) \ {c}) < 2}) >> 
        :c \in useful }

CardsBlockingPower == CalcBlockingPower(AiPartialWinningSets, BlockingCards)

MaxBlockingPower(cardsWithPower) == MaxInSet({ c[2]: c \in cardsWithPower })

AIHasWon(hand) == (\E winningSet \in winningSets: winningSet \subseteq hand)
PlayerHasWon(hand) == (\E winningSet \in winningSets: winningSet \subseteq hand)
IsADraw(remaining) == (Cardinality(remaining) = 0)

GetResult(aihand, playerhand, remaining) == CASE AIHasWon(aihand) -> "ai wins"
            [] PlayerHasWon(playerhand) -> "player wins"
            [] IsADraw(remaining) -> "draw"
            [] OTHER -> "playing"

result == GetResult(ai, player, remainingCards)

TakeCardAI ==
    LET 
        aiCard == nextRandom
    IN 
        /\ ai' = ai \union { aiCard }
        /\ remainingCards' = remainingCards \ { aiCard }
        /\ player' = player
        /\ playing' = "player"
        /\ nextRandom' = IF Cardinality(remainingCards') = 0 
            THEN 0 
            ELSE RandomElement(remainingCards')

OppositeCorner(c) == 
        CASE 
            c = 2 -> 8
            [] c = 8 -> 2 
            [] c = 4 -> 6
            [] OTHER -> 4
            
TakeCardPlayer ==
    LET cbp == CalcBlockingPower(AiPartialWinningSets, BlockingCards)
        playerCard == 
        CASE 
            \* we have a winning card available, take it
            Cardinality(PlayerWinningCards) > 0 -> 
                CHOOSE c \in PlayerWinningCards: TRUE

            \* block AI win
            [] Cardinality(AiWinningCards) = 1 -> 
                CHOOSE c \in AiWinningCards: TRUE

            \* we're starting, choose first card
            [] (Cardinality(ai) = 0) -> 
                CHOOSE c \in corners: TRUE

            \* AI started, choose first card
            [] (Cardinality(ai) = 1) /\ (Cardinality(player) = 0) ->
                CASE 
                    \* AI chose 5, choose a corner
                    (5 \in ai) -> CHOOSE c \in corners: TRUE
                    \* AI chose a corner, choose centre
                    [] (ai \subseteq corners) -> 5
                    \* AI took an edge, also choose 5
                    [] OTHER -> 5

            \* AI started and we're choosing second card
            [] (Cardinality(ai) = 2) /\ (Cardinality(player) = 1) ->
                CASE 
                    \* AI has a corner and center, choose a remaining corner
                    (\E c \in ai: c \in corners) /\ (\E c \in ai: c \in centre) -> 
                       CHOOSE c \in corners: c \in remainingCards
                    \* AI has a corner and we have center, 
                    \*  choose an edge that is part of a winning set in play
                    [] (\E c \in ai: c \in corners) /\ (\E c \in player: c \in centre) -> 
                        CHOOSE c \in (edges \intersect remainingCards): 
                            \E ws \in PlayerWinningSetsInPlay: c \in ws
                    [] OTHER ->
                        \* AI started center or edge, just block from here
                        (CHOOSE c \in cbp: c[2] = MaxBlockingPower(cbp))[1]

            \* we started, choose second card
            [] (Cardinality(ai) = 1) /\ (Cardinality(player) = 1) ->
                IF
                    \* we have a corner and AI has centre, choose opposite corner
                    ((5 \in ai) \/ (ai \subseteq edges)) /\ (player \subseteq corners) 
                THEN 
                    OppositeCorner(CHOOSE c \in player: TRUE)
                ELSE (CHOOSE c \in PlayerUsefulCardsPower: c[2] = PlayerMaxPower)[1]
                        
            \* only 1 card left, take it
            [] Cardinality(remainingCards) = 1 -> 
                CHOOSE c \in remainingCards: TRUE

            [] OTHER ->
                IF Cardinality(ai) > Cardinality(player) THEN 
                    \* defending
                    (CHOOSE c \in cbp: c[2] = MaxBlockingPower(cbp))[1]
                ELSE
                    IF Cardinality(PlayerUsefulCardsPower) = 0
                    THEN 
                        1
                    ELSE
                        (CHOOSE c \in PlayerUsefulCardsPower: c[2] = PlayerMaxPower)[1]
    IN 
        /\ remainingCards' = remainingCards \ { playerCard }
        /\ player' = player \union { playerCard }
        /\ ai' = ai
        /\ playing' = "ai"
        /\ nextRandom' = IF Cardinality(remainingCards') = 0 
            THEN 0 
            ELSE RandomElement(remainingCards')
                
Restart == 
    /\ remainingCards' = {1,2,3,4,5,6,7,8,9}
    /\ player' = {} 
    /\ ai' = {}
    /\ playing' = IF 1 \in RandomSubset(1, {1,2}) THEN "ai" ELSE "player"
    /\ nextRandom' = RandomElement(remainingCards')

Init == 
    /\ remainingCards = {1,2,3,4,5,6,7,8,9}
    /\ player = {} 
    /\ ai = {}
    /\ playing = IF 1 \in RandomSubset(1, {1,2}) THEN "ai" ELSE "player"
    /\ nextRandom = RandomElement(remainingCards)

Next == \/ (result = "playing" /\ playing = "ai" /\ TakeCardAI)
        \/ (result = "playing" /\ playing = "player" /\ TakeCardPlayer)
        \/ (~(result = "playing") /\ Restart)

Spec == Init /\ [][Next]_vars

NotSolved == 
    /\ ~AIHasWon(ai)
    /\ ~PlayerHasWon(player)
    /\ ~IsADraw(remainingCards)

AINeverWins == []~AIHasWon(ai)

THEOREM Spec => AINeverWins

=============================================================================
