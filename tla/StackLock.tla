 ----------------- MODULE StackLock  ----------------
EXTENDS Naturals, TLC, Sequences

CONSTANT NUM_PROCESSES
CONSTANT NUM_LOOPS

(*--fair algorithm lockAlg
    variables
        Stack = <<>>,
        Lock = FALSE,
        Nodes = [ self \in ProcSet |-> defaultInitValue ];
        
    macro init_node(N) begin
        Nodes[N] := FALSE;
    end macro;

    macro wait(N) begin
        await Nodes[N];
        Nodes[N] := defaultInitValue;
    end macro;
    
    macro signal(N) begin
        assert Nodes[N] = FALSE;
        Nodes[N] := TRUE;
    end macro;

    macro push(Stack, N) begin
        Stack := <<N>> \o Stack;
    end macro;
    
    macro pop(Stack, Popped) begin
        Popped := Head(Stack);
        Stack := Tail(Stack);
    end macro;
    
    procedure lock()
    begin
    PUSH_NODE:
        if Lock then
            init_node(self);
            push(Stack, self);
        WAIT:
            wait(self);
        else
            Lock := TRUE;
        end if;
    RET:
        return;
    end procedure;
    
    procedure unlock()
        variables Popped;
    begin
    UNLOCK:
        assert Lock;
        if Stack = <<>> then
            Lock := FALSE;
        else
            pop(Stack, Popped);
        SIGNAL:
            signal(Popped);
        end if;
    RET:
        return;
    end procedure
    
    fair process p \in 1..NUM_PROCESSES
        variables Counter = 0;
    begin
    LOOP:
        while Counter < NUM_LOOPS do
            call lock();
        CS:
            assert \A i \in 1..NUM_PROCESSES : (i = self) <=> (pc[i] = "CS");
        UNLOCK:
            call unlock();
        COUNT:
            Counter := Counter + 1;
        end while;
    end process;
end algorithm;
*)
\* BEGIN TRANSLATION
\* Label RET of procedure lock at line 48 col 9 changed to RET_
\* Label UNLOCK of procedure unlock at line 55 col 9 changed to UNLOCK_
CONSTANT defaultInitValue
VARIABLES Stack, Lock, Nodes, pc, stack, Popped, Counter

vars == << Stack, Lock, Nodes, pc, stack, Popped, Counter >>

ProcSet == (1..NUM_PROCESSES)

Init == (* Global variables *)
        /\ Stack = <<>>
        /\ Lock = FALSE
        /\ Nodes = [ self \in ProcSet |-> defaultInitValue ]
        (* Procedure unlock *)
        /\ Popped = [ self \in ProcSet |-> defaultInitValue]
        (* Process p *)
        /\ Counter = [self \in 1..NUM_PROCESSES |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "LOOP"]

PUSH_NODE(self) == /\ pc[self] = "PUSH_NODE"
                   /\ IF Lock
                         THEN /\ Nodes' = [Nodes EXCEPT ![self] = FALSE]
                              /\ Stack' = <<self>> \o Stack
                              /\ pc' = [pc EXCEPT ![self] = "WAIT"]
                              /\ Lock' = Lock
                         ELSE /\ Lock' = TRUE
                              /\ pc' = [pc EXCEPT ![self] = "RET_"]
                              /\ UNCHANGED << Stack, Nodes >>
                   /\ UNCHANGED << stack, Popped, Counter >>

WAIT(self) == /\ pc[self] = "WAIT"
              /\ Nodes[self]
              /\ Nodes' = [Nodes EXCEPT ![self] = defaultInitValue]
              /\ pc' = [pc EXCEPT ![self] = "RET_"]
              /\ UNCHANGED << Stack, Lock, stack, Popped, Counter >>

RET_(self) == /\ pc[self] = "RET_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Stack, Lock, Nodes, Popped, Counter >>

lock(self) == PUSH_NODE(self) \/ WAIT(self) \/ RET_(self)

UNLOCK_(self) == /\ pc[self] = "UNLOCK_"
                 /\ Assert(Lock, 
                           "Failure of assertion at line 55, column 9.")
                 /\ IF Stack = <<>>
                       THEN /\ Lock' = FALSE
                            /\ pc' = [pc EXCEPT ![self] = "RET"]
                            /\ UNCHANGED << Stack, Popped >>
                       ELSE /\ Popped' = [Popped EXCEPT ![self] = Head(Stack)]
                            /\ Stack' = Tail(Stack)
                            /\ pc' = [pc EXCEPT ![self] = "SIGNAL"]
                            /\ Lock' = Lock
                 /\ UNCHANGED << Nodes, stack, Counter >>

SIGNAL(self) == /\ pc[self] = "SIGNAL"
                /\ Assert(Nodes[Popped[self]] = FALSE, 
                          "Failure of assertion at line 23, column 9 of macro called at line 61, column 13.")
                /\ Nodes' = [Nodes EXCEPT ![Popped[self]] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "RET"]
                /\ UNCHANGED << Stack, Lock, stack, Popped, Counter >>

RET(self) == /\ pc[self] = "RET"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ Popped' = [Popped EXCEPT ![self] = Head(stack[self]).Popped]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Stack, Lock, Nodes, Counter >>

unlock(self) == UNLOCK_(self) \/ SIGNAL(self) \/ RET(self)

LOOP(self) == /\ pc[self] = "LOOP"
              /\ IF Counter[self] < NUM_LOOPS
                    THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                                  pc        |->  "CS" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "PUSH_NODE"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ stack' = stack
              /\ UNCHANGED << Stack, Lock, Nodes, Popped, Counter >>

CS(self) == /\ pc[self] = "CS"
            /\ Assert(\A i \in 1..NUM_PROCESSES : (i = self) <=> (pc[i] = "CS"), 
                      "Failure of assertion at line 74, column 13.")
            /\ pc' = [pc EXCEPT ![self] = "UNLOCK"]
            /\ UNCHANGED << Stack, Lock, Nodes, stack, Popped, Counter >>

UNLOCK(self) == /\ pc[self] = "UNLOCK"
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                         pc        |->  "COUNT",
                                                         Popped    |->  Popped[self] ] >>
                                                     \o stack[self]]
                /\ Popped' = [Popped EXCEPT ![self] = defaultInitValue]
                /\ pc' = [pc EXCEPT ![self] = "UNLOCK_"]
                /\ UNCHANGED << Stack, Lock, Nodes, Counter >>

COUNT(self) == /\ pc[self] = "COUNT"
               /\ Counter' = [Counter EXCEPT ![self] = Counter[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "LOOP"]
               /\ UNCHANGED << Stack, Lock, Nodes, stack, Popped >>

p(self) == LOOP(self) \/ CS(self) \/ UNLOCK(self) \/ COUNT(self)

Next == (\E self \in ProcSet: lock(self) \/ unlock(self))
           \/ (\E self \in 1..NUM_PROCESSES: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in 1..NUM_PROCESSES : WF_vars(p(self)) /\ WF_vars(lock(self)) /\ WF_vars(unlock(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
