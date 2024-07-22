---- MODULE Verona ----
EXTENDS Naturals, Sequences

CONSTANTS ReadMode, WriteMode
Modes == {ReadMode, WriteMode}

CONSTANTS Cowns, Behaviors

VARIABLES
    behaviorDependencies,
    behaviorIsExecuting,
    behaviorIsDone
vars == <<behaviorDependencies, behaviorIsExecuting, behaviorIsDone>>

Dependencies == [
    mode: Modes,
    cown: Cowns
]

TypeOk ==
    /\ behaviorDependencies \in [Behavior |-> Dependencies]
    /\ behaviorIsExecuting \in [Behavior |-> BOOLEAN]
    /\ behaviorIsDone \in [Behavior |-> BOOLEAN]

Init ==
    /\ behaviorIsExecuting = [b \in Behaviors |-> FALSE]
    /\ behaviorIsDone = [b \in Behaviors |-> FALSE]
    /\ behaviorDependencies = [b \in Behaviors |->
        LET deps == CHOOSE deps \in SUBSET Cowns : TRUE
        IN  { [mode |-> WriteMode, cown |-> cown] : cown \in deps }
       ]

BehaviorStart(b) ==
    /\ behaviorIsDone[b] = FALSE
    /\ behaviorIsExecuting[b] = FALSE
    /\ \A dep \in behaviorDependencies[b] :
        \lnot \E b2 \in Behaviors :
            /\ b2 # b
            /\ behaviorIsExecuting[b2]
            /\ \E dep2 \in behaviorDependencies[b2] :
                dep.cown = dep2.cown
    /\ behaviorIsExecuting' = [behaviorIsExecuting EXCEPT ![b] = TRUE]
    /\ UNCHANGED <<behaviorIsDone, behaviorDependencies>>

BehaviorEnd(b) ==
    /\ behaviorIsExecuting[b] = TRUE
    /\ behaviorIsExecuting' = [behaviorIsExecuting EXCEPT ![b] = FALSE]
    /\ behaviorIsDone' = [behaviorIsDone EXCEPT ![b] = TRUE]
    /\ UNCHANGED behaviorDependencies

Next ==
    \/ \E b \in Behaviors :
        \/ BehaviorStart(b)
        \/ BehaviorEnd(b)
    \/ \A b \in Behaviors :
        /\ behaviorIsDone[b]
        /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* correctness

BehaviorTermination ==
    \A b \in Behaviors :
        behaviorIsExecuting[b] ~> [](\lnot behaviorIsExecuting[b])

BehaviorOneShot ==
    \A b \in Behaviors :
        [](behaviorIsDone[b] => [](behaviorIsDone[b] /\ ~behaviorIsExecuting[b]))

====