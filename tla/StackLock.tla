 ----------------- MODULE StackLock  ----------------
EXTENDS Naturals, TLC, Sequences

CONSTANT NUM_PROCESSES
CONSTANT NUM_LOOPS

(*--algorithm lockAlg
    variables
        Locks = [
            Stack |-> [ LockId \in 1..NUM_LOCKS |-> <<>> ],
            Lock |-> [ LockId \in 1..NUM_LOCKS |-> FALSE ]
            ],
        Nodes = [ self \in ProcSet |-> defaultInitValue ];
    
    define
        NULL == 0
        NUM_LOCKS == 1
        L == 1
    end define;

    macro try_acquire(Result, Lock)
    begin
        if Locks.Lock[Lock] then
            Result := FALSE;
        else
            Locks.Lock[Lock] := TRUE;
            Result := TRUE;
        end if;
    end macro;
    
    macro release(Lock)
    begin
        assert Locks.Lock[Lock];
        Locks.Lock[Lock] := FALSE;
    end macro;
    
    macro pop(Popped, Stack)
    begin
        if Locks.Stack[Stack] = <<>> then
            Popped := NULL;
        else
            Popped := Head(Locks.Stack[Stack]);
            Locks.Stack[Stack] := Tail(Locks.Stack[Stack]);
        end if;
    end macro;
    
    macro push(Stack, Node)
    begin
        Locks.Stack[Stack] := <<Node>> \o Locks.Stack[Stack];
    end macro;

    macro wait(Node)
    begin
        await Nodes[self];
        Nodes[self] := NULL;
    end macro;
    
    macro signal(Node)
    begin
        assert Nodes[Node] = FALSE;
        Nodes[Node] := TRUE;
    end macro;

    procedure lock(Lock)
        variables Acquired, Counter = 0;
    begin
    ATTEMPT_ACQUIRE:
        while Counter < 4 do
            try_acquire(Acquired, Lock);
            if Acquired then
                RET: return;
            end if;
        UPDATE_COUNTER:
            Counter := Counter + 1;
        end while;
    PUSH_NODE:
        Nodes[self] := FALSE;
        push(Lock, self);
    FLUSH_LOCK:
        call flush(Lock);
    WAIT:
        wait(self);
        return;
    end procedure;
    
    procedure unlock(Lock)
        variables Popped;
    begin
    POP:
        pop(Popped, Lock);
        if Popped /= NULL then
            signal(Popped);
            RET: return;
        end if;
    RELEASE:
        release(Lock);
    FLUSH_LOCK:
        call flush(Lock);
        return;
    end procedure;
    
    procedure flush(Lock)
        variables Popped, Acquired;
    begin
    LOOP:
        while Locks.Stack[Lock] /= <<>> do
        TRY_ACQUIRE:
            try_acquire(Acquired, Lock);
            if ~Acquired then
                RET: return;
            end if;
        POP:
            pop(Popped, Lock);
        CHECK_POP:
            if Popped /= NULL then
                signal(Popped);
                return;
            end if;
        RELEASE:
            release(Lock);
        end while;
        return;
    end procedure;
    
    fair process p \in 1..NUM_PROCESSES
        variables Counter = 0;
    begin
    LOOP:
        while Counter < NUM_LOOPS do
            call lock(L);
        CS:
            assert \A i \in 1..NUM_PROCESSES : (i = self) <=> (pc[i] = "CS");
        UNLOCK:
            call unlock(L);
        COUNT:
            Counter := Counter + 1;
        end while;
    end process;
end algorithm;
*)
\* BEGIN TRANSLATION
\* Label RET of procedure lock at line 71 col 22 changed to RET_
\* Label FLUSH_LOCK of procedure lock at line 80 col 9 changed to FLUSH_LOCK_
\* Label POP of procedure unlock at line 39 col 9 changed to POP_
\* Label RET of procedure unlock at line 93 col 18 changed to RET_u
\* Label RELEASE of procedure unlock at line 33 col 9 changed to RELEASE_
\* Label LOOP of procedure flush at line 106 col 9 changed to LOOP_
\* Process variable Counter of process p at line 126 col 19 changed to Counter_
\* Procedure variable Acquired of procedure lock at line 65 col 19 changed to Acquired_
\* Procedure variable Popped of procedure unlock at line 87 col 19 changed to Popped_
\* Parameter Lock of procedure lock at line 64 col 20 changed to Lock_
\* Parameter Lock of procedure unlock at line 86 col 22 changed to Lock_u
CONSTANT defaultInitValue
VARIABLES Locks, Nodes, pc, stack

(* define statement *)
NULL == 0
NUM_LOCKS == 1
L == 1

VARIABLES Lock_, Acquired_, Counter, Lock_u, Popped_, Lock, Popped, Acquired, 
          Counter_

vars == << Locks, Nodes, pc, stack, Lock_, Acquired_, Counter, Lock_u, 
           Popped_, Lock, Popped, Acquired, Counter_ >>

ProcSet == (1..NUM_PROCESSES)

Init == (* Global variables *)
        /\ Locks =     [
                   Stack |-> [ LockId \in 1..NUM_LOCKS |-> <<>> ],
                   Lock |-> [ LockId \in 1..NUM_LOCKS |-> FALSE ]
                   ]
        /\ Nodes = [ self \in ProcSet |-> defaultInitValue ]
        (* Procedure lock *)
        /\ Lock_ = [ self \in ProcSet |-> defaultInitValue]
        /\ Acquired_ = [ self \in ProcSet |-> defaultInitValue]
        /\ Counter = [ self \in ProcSet |-> 0]
        (* Procedure unlock *)
        /\ Lock_u = [ self \in ProcSet |-> defaultInitValue]
        /\ Popped_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure flush *)
        /\ Lock = [ self \in ProcSet |-> defaultInitValue]
        /\ Popped = [ self \in ProcSet |-> defaultInitValue]
        /\ Acquired = [ self \in ProcSet |-> defaultInitValue]
        (* Process p *)
        /\ Counter_ = [self \in 1..NUM_PROCESSES |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "LOOP"]

ATTEMPT_ACQUIRE(self) == /\ pc[self] = "ATTEMPT_ACQUIRE"
                         /\ IF Counter[self] < 4
                               THEN /\ IF Locks.Lock[Lock_[self]]
                                          THEN /\ Acquired_' = [Acquired_ EXCEPT ![self] = FALSE]
                                               /\ Locks' = Locks
                                          ELSE /\ Locks' = [Locks EXCEPT !.Lock[Lock_[self]] = TRUE]
                                               /\ Acquired_' = [Acquired_ EXCEPT ![self] = TRUE]
                                    /\ IF Acquired_'[self]
                                          THEN /\ pc' = [pc EXCEPT ![self] = "RET_"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "UPDATE_COUNTER"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "PUSH_NODE"]
                                    /\ UNCHANGED << Locks, Acquired_ >>
                         /\ UNCHANGED << Nodes, stack, Lock_, Counter, Lock_u, 
                                         Popped_, Lock, Popped, Acquired, 
                                         Counter_ >>

UPDATE_COUNTER(self) == /\ pc[self] = "UPDATE_COUNTER"
                        /\ Counter' = [Counter EXCEPT ![self] = Counter[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "ATTEMPT_ACQUIRE"]
                        /\ UNCHANGED << Locks, Nodes, stack, Lock_, Acquired_, 
                                        Lock_u, Popped_, Lock, Popped, 
                                        Acquired, Counter_ >>

RET_(self) == /\ pc[self] = "RET_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ Acquired_' = [Acquired_ EXCEPT ![self] = Head(stack[self]).Acquired_]
              /\ Counter' = [Counter EXCEPT ![self] = Head(stack[self]).Counter]
              /\ Lock_' = [Lock_ EXCEPT ![self] = Head(stack[self]).Lock_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Locks, Nodes, Lock_u, Popped_, Lock, Popped, 
                              Acquired, Counter_ >>

PUSH_NODE(self) == /\ pc[self] = "PUSH_NODE"
                   /\ Nodes' = [Nodes EXCEPT ![self] = FALSE]
                   /\ Locks' = [Locks EXCEPT !.Stack[Lock_[self]] = <<self>> \o Locks.Stack[Lock_[self]]]
                   /\ pc' = [pc EXCEPT ![self] = "FLUSH_LOCK_"]
                   /\ UNCHANGED << stack, Lock_, Acquired_, Counter, Lock_u, 
                                   Popped_, Lock, Popped, Acquired, Counter_ >>

FLUSH_LOCK_(self) == /\ pc[self] = "FLUSH_LOCK_"
                     /\ /\ Lock' = [Lock EXCEPT ![self] = Lock_[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flush",
                                                                 pc        |->  "WAIT",
                                                                 Popped    |->  Popped[self],
                                                                 Acquired  |->  Acquired[self],
                                                                 Lock      |->  Lock[self] ] >>
                                                             \o stack[self]]
                     /\ Popped' = [Popped EXCEPT ![self] = defaultInitValue]
                     /\ Acquired' = [Acquired EXCEPT ![self] = defaultInitValue]
                     /\ pc' = [pc EXCEPT ![self] = "LOOP_"]
                     /\ UNCHANGED << Locks, Nodes, Lock_, Acquired_, Counter, 
                                     Lock_u, Popped_, Counter_ >>

WAIT(self) == /\ pc[self] = "WAIT"
              /\ Nodes[self]
              /\ Nodes' = [Nodes EXCEPT ![self] = NULL]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ Acquired_' = [Acquired_ EXCEPT ![self] = Head(stack[self]).Acquired_]
              /\ Counter' = [Counter EXCEPT ![self] = Head(stack[self]).Counter]
              /\ Lock_' = [Lock_ EXCEPT ![self] = Head(stack[self]).Lock_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Locks, Lock_u, Popped_, Lock, Popped, Acquired, 
                              Counter_ >>

lock(self) == ATTEMPT_ACQUIRE(self) \/ UPDATE_COUNTER(self) \/ RET_(self)
                 \/ PUSH_NODE(self) \/ FLUSH_LOCK_(self) \/ WAIT(self)

POP_(self) == /\ pc[self] = "POP_"
              /\ IF Locks.Stack[Lock_u[self]] = <<>>
                    THEN /\ Popped_' = [Popped_ EXCEPT ![self] = NULL]
                         /\ Locks' = Locks
                    ELSE /\ Popped_' = [Popped_ EXCEPT ![self] = Head(Locks.Stack[Lock_u[self]])]
                         /\ Locks' = [Locks EXCEPT !.Stack[Lock_u[self]] = Tail(Locks.Stack[Lock_u[self]])]
              /\ IF Popped_'[self] /= NULL
                    THEN /\ Assert(Nodes[Popped_'[self]] = FALSE, 
                                   "Failure of assertion at line 60, column 9 of macro called at line 92, column 13.")
                         /\ Nodes' = [Nodes EXCEPT ![Popped_'[self]] = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = "RET_u"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "RELEASE_"]
                         /\ Nodes' = Nodes
              /\ UNCHANGED << stack, Lock_, Acquired_, Counter, Lock_u, Lock, 
                              Popped, Acquired, Counter_ >>

RET_u(self) == /\ pc[self] = "RET_u"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ Popped_' = [Popped_ EXCEPT ![self] = Head(stack[self]).Popped_]
               /\ Lock_u' = [Lock_u EXCEPT ![self] = Head(stack[self]).Lock_u]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Locks, Nodes, Lock_, Acquired_, Counter, Lock, 
                               Popped, Acquired, Counter_ >>

RELEASE_(self) == /\ pc[self] = "RELEASE_"
                  /\ Assert(Locks.Lock[Lock_u[self]], 
                            "Failure of assertion at line 33, column 9 of macro called at line 96, column 9.")
                  /\ Locks' = [Locks EXCEPT !.Lock[Lock_u[self]] = FALSE]
                  /\ pc' = [pc EXCEPT ![self] = "FLUSH_LOCK"]
                  /\ UNCHANGED << Nodes, stack, Lock_, Acquired_, Counter, 
                                  Lock_u, Popped_, Lock, Popped, Acquired, 
                                  Counter_ >>

FLUSH_LOCK(self) == /\ pc[self] = "FLUSH_LOCK"
                    /\ /\ Lock' = [Lock EXCEPT ![self] = Lock_u[self]]
                       /\ Popped_' = [Popped_ EXCEPT ![self] = Head(stack[self]).Popped_]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flush",
                                                                pc        |->  Head(stack[self]).pc,
                                                                Popped    |->  Popped[self],
                                                                Acquired  |->  Acquired[self],
                                                                Lock      |->  Lock[self] ] >>
                                                            \o Tail(stack[self])]
                    /\ Popped' = [Popped EXCEPT ![self] = defaultInitValue]
                    /\ Acquired' = [Acquired EXCEPT ![self] = defaultInitValue]
                    /\ pc' = [pc EXCEPT ![self] = "LOOP_"]
                    /\ UNCHANGED << Locks, Nodes, Lock_, Acquired_, Counter, 
                                    Lock_u, Counter_ >>

unlock(self) == POP_(self) \/ RET_u(self) \/ RELEASE_(self)
                   \/ FLUSH_LOCK(self)

LOOP_(self) == /\ pc[self] = "LOOP_"
               /\ IF Locks.Stack[Lock[self]] /= <<>>
                     THEN /\ pc' = [pc EXCEPT ![self] = "TRY_ACQUIRE"]
                          /\ UNCHANGED << stack, Lock, Popped, Acquired >>
                     ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ Popped' = [Popped EXCEPT ![self] = Head(stack[self]).Popped]
                          /\ Acquired' = [Acquired EXCEPT ![self] = Head(stack[self]).Acquired]
                          /\ Lock' = [Lock EXCEPT ![self] = Head(stack[self]).Lock]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Locks, Nodes, Lock_, Acquired_, Counter, Lock_u, 
                               Popped_, Counter_ >>

TRY_ACQUIRE(self) == /\ pc[self] = "TRY_ACQUIRE"
                     /\ IF Locks.Lock[Lock[self]]
                           THEN /\ Acquired' = [Acquired EXCEPT ![self] = FALSE]
                                /\ Locks' = Locks
                           ELSE /\ Locks' = [Locks EXCEPT !.Lock[Lock[self]] = TRUE]
                                /\ Acquired' = [Acquired EXCEPT ![self] = TRUE]
                     /\ IF ~Acquired'[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = "RET"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "POP"]
                     /\ UNCHANGED << Nodes, stack, Lock_, Acquired_, Counter, 
                                     Lock_u, Popped_, Lock, Popped, Counter_ >>

RET(self) == /\ pc[self] = "RET"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ Popped' = [Popped EXCEPT ![self] = Head(stack[self]).Popped]
             /\ Acquired' = [Acquired EXCEPT ![self] = Head(stack[self]).Acquired]
             /\ Lock' = [Lock EXCEPT ![self] = Head(stack[self]).Lock]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Locks, Nodes, Lock_, Acquired_, Counter, Lock_u, 
                             Popped_, Counter_ >>

POP(self) == /\ pc[self] = "POP"
             /\ IF Locks.Stack[Lock[self]] = <<>>
                   THEN /\ Popped' = [Popped EXCEPT ![self] = NULL]
                        /\ Locks' = Locks
                   ELSE /\ Popped' = [Popped EXCEPT ![self] = Head(Locks.Stack[Lock[self]])]
                        /\ Locks' = [Locks EXCEPT !.Stack[Lock[self]] = Tail(Locks.Stack[Lock[self]])]
             /\ pc' = [pc EXCEPT ![self] = "CHECK_POP"]
             /\ UNCHANGED << Nodes, stack, Lock_, Acquired_, Counter, Lock_u, 
                             Popped_, Lock, Acquired, Counter_ >>

CHECK_POP(self) == /\ pc[self] = "CHECK_POP"
                   /\ IF Popped[self] /= NULL
                         THEN /\ Assert(Nodes[Popped[self]] = FALSE, 
                                        "Failure of assertion at line 60, column 9 of macro called at line 116, column 17.")
                              /\ Nodes' = [Nodes EXCEPT ![Popped[self]] = TRUE]
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ Popped' = [Popped EXCEPT ![self] = Head(stack[self]).Popped]
                              /\ Acquired' = [Acquired EXCEPT ![self] = Head(stack[self]).Acquired]
                              /\ Lock' = [Lock EXCEPT ![self] = Head(stack[self]).Lock]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "RELEASE"]
                              /\ UNCHANGED << Nodes, stack, Lock, Popped, 
                                              Acquired >>
                   /\ UNCHANGED << Locks, Lock_, Acquired_, Counter, Lock_u, 
                                   Popped_, Counter_ >>

RELEASE(self) == /\ pc[self] = "RELEASE"
                 /\ Assert(Locks.Lock[Lock[self]], 
                           "Failure of assertion at line 33, column 9 of macro called at line 120, column 13.")
                 /\ Locks' = [Locks EXCEPT !.Lock[Lock[self]] = FALSE]
                 /\ pc' = [pc EXCEPT ![self] = "LOOP_"]
                 /\ UNCHANGED << Nodes, stack, Lock_, Acquired_, Counter, 
                                 Lock_u, Popped_, Lock, Popped, Acquired, 
                                 Counter_ >>

flush(self) == LOOP_(self) \/ TRY_ACQUIRE(self) \/ RET(self) \/ POP(self)
                  \/ CHECK_POP(self) \/ RELEASE(self)

LOOP(self) == /\ pc[self] = "LOOP"
              /\ IF Counter_[self] < NUM_LOOPS
                    THEN /\ /\ Lock_' = [Lock_ EXCEPT ![self] = L]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                                     pc        |->  "CS",
                                                                     Acquired_ |->  Acquired_[self],
                                                                     Counter   |->  Counter[self],
                                                                     Lock_     |->  Lock_[self] ] >>
                                                                 \o stack[self]]
                         /\ Acquired_' = [Acquired_ EXCEPT ![self] = defaultInitValue]
                         /\ Counter' = [Counter EXCEPT ![self] = 0]
                         /\ pc' = [pc EXCEPT ![self] = "ATTEMPT_ACQUIRE"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << stack, Lock_, Acquired_, Counter >>
              /\ UNCHANGED << Locks, Nodes, Lock_u, Popped_, Lock, Popped, 
                              Acquired, Counter_ >>

CS(self) == /\ pc[self] = "CS"
            /\ Assert(\A i \in 1..NUM_PROCESSES : (i = self) <=> (pc[i] = "CS"), 
                      "Failure of assertion at line 132, column 13.")
            /\ pc' = [pc EXCEPT ![self] = "UNLOCK"]
            /\ UNCHANGED << Locks, Nodes, stack, Lock_, Acquired_, Counter, 
                            Lock_u, Popped_, Lock, Popped, Acquired, Counter_ >>

UNLOCK(self) == /\ pc[self] = "UNLOCK"
                /\ /\ Lock_u' = [Lock_u EXCEPT ![self] = L]
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                            pc        |->  "COUNT",
                                                            Popped_   |->  Popped_[self],
                                                            Lock_u    |->  Lock_u[self] ] >>
                                                        \o stack[self]]
                /\ Popped_' = [Popped_ EXCEPT ![self] = defaultInitValue]
                /\ pc' = [pc EXCEPT ![self] = "POP_"]
                /\ UNCHANGED << Locks, Nodes, Lock_, Acquired_, Counter, Lock, 
                                Popped, Acquired, Counter_ >>

COUNT(self) == /\ pc[self] = "COUNT"
               /\ Counter_' = [Counter_ EXCEPT ![self] = Counter_[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "LOOP"]
               /\ UNCHANGED << Locks, Nodes, stack, Lock_, Acquired_, Counter, 
                               Lock_u, Popped_, Lock, Popped, Acquired >>

p(self) == LOOP(self) \/ CS(self) \/ UNLOCK(self) \/ COUNT(self)

Next == (\E self \in ProcSet: lock(self) \/ unlock(self) \/ flush(self))
           \/ (\E self \in 1..NUM_PROCESSES: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NUM_PROCESSES : /\ WF_vars(p(self))
                                          /\ WF_vars(lock(self))
                                          /\ WF_vars(unlock(self))
                                          /\ WF_vars(flush(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
