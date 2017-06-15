 ----------------- MODULE StackLock  ----------------
EXTENDS Naturals, TLC, Sequences

CONSTANT NUM_PROCESSES
CONSTANT SHOULD_LOG

(*--fair algorithm lockAlg
    variables
        Locks = [
            Stack |-> [ LockId \in 1..NUM_LOCKS |-> <<>> ],
            Lock |-> [ LockId \in 1..NUM_LOCKS |-> FALSE ]
            ],
        rVal = [ Id \in 1..NUM_PROCESSES |-> defaultInitValue ],
        Nodes = [ Id \in 1..NUM_PROCESSES |-> defaultInitValue ];
    
    define
        NULL == 0
        NUM_LOCKS == 1
        L == 1
    end define;

    macro LOG(ToLog)
    begin
        if SHOULD_LOG then
            print ToLog;
        end if;
    end macro;
        
    macro TRACE(ToLog)
    begin
        LOG(<<self, Head(stack[self])["procedure"]>> \o ToLog);
    end macro;
    
    procedure lock(Lock)
    begin
        PUSH_NODE:
            TRACE(<<>>);
            Nodes[self] := FALSE;
            call push(Lock, self);
        FLUSH_LOCK:
            call flush(Lock);
        WAIT:
            call wait(self);
            return;
    end procedure;
    
    procedure unlock(Lock)
    begin
        POP:
            TRACE(<<>>);
            call pop(Lock);
        CHECK_POP:
            if rVal[self] /= NULL then
                call signal(rVal[self]);
                return;
            end if;
        RELEASE:
            call release(Lock);
        FLUSH_LOCK:
            call flush(Lock);
            return;
    end procedure;
    
    procedure flush(Lock)
    begin
        DEBUG:
            TRACE(<<>>);
        LOOP:
            while Locks.Stack[Lock] /= <<>> do
                TRY_ACQUIRE:
                    call try_acquire(Lock);
                CHECK_ACQUIRE:
                    if ~rVal[self] then
                        return;
                    end if;
                POP:
                    call pop(Lock);
                CHECK_POP:
                    if rVal[self]/= NULL then
                        call signal(rVal[self]);
                        return;
                    end if;
                RELEASE:
                    call release(Lock);
             end while;
             return;
    end procedure;
    
    procedure try_acquire(Lock)
    begin
        A:
            TRACE(<<Locks.Lock[Lock]>>);
            if Locks.Lock[Lock] then
                rVal[self] := FALSE;
            else
                Locks.Lock[Lock] := TRUE;
                rVal[self] := TRUE;
            end if;
            return;
    end procedure;
    
    procedure release(Lock)
    begin
        A:
            TRACE(<<>>);
            assert Locks.Lock[Lock];
            Locks.Lock[Lock] := FALSE;
            return;
    end procedure;
    
    procedure push(Stack, Node)
    begin
        A:
            TRACE(<<>>);
            Locks.Stack[Stack] := <<Node>> \o Locks.Stack[Stack];
            return;
    end procedure;
    
    procedure pop(Stack)
    begin
        A:
            TRACE(<<>>);
            if Locks.Stack[Stack] = <<>> then
                rVal[self] := NULL;
            else
                rVal[self] := Head(Locks.Stack[Stack]);
                Locks.Stack[Stack] := Tail(Locks.Stack[Stack]);
            end if;
            return;
    end procedure;

    procedure wait(Node)
    begin
        A:
            TRACE(<<>>);
            await Nodes[self];
            Nodes[self] := NULL;
            return;
    end procedure;
    
    procedure signal(Node)
    begin
        A:
            TRACE(<<>>);
            assert Nodes[Node] = FALSE;
            Nodes[Node] := TRUE;
            return;
    end procedure;
    
    fair+ process p \in 1..NUM_PROCESSES
    begin
        LOCK:
            LOG(<<self, "start">>); 
            call lock(L);
        CS:
            assert \A i \in 1..NUM_PROCESSES : (i = self) <=> (pc[i] = "CS");
        UNLOCK:
            call unlock(L);
        DEBUG_END:
            LOG(<<self, "finish">>); 
    end process;
end algorithm;
*)
\* BEGIN TRANSLATION
\* Label FLUSH_LOCK of procedure lock at line 41 col 13 changed to FLUSH_LOCK_
\* Label POP of procedure unlock at line 24 col 9 changed to POP_
\* Label CHECK_POP of procedure unlock at line 53 col 13 changed to CHECK_POP_
\* Label RELEASE of procedure unlock at line 58 col 13 changed to RELEASE_
\* Label A of procedure try_acquire at line 24 col 9 changed to A_
\* Label A of procedure release at line 24 col 9 changed to A_r
\* Label A of procedure push at line 24 col 9 changed to A_p
\* Label A of procedure pop at line 24 col 9 changed to A_po
\* Label A of procedure wait at line 24 col 9 changed to A_w
\* Parameter Lock of procedure lock at line 34 col 20 changed to Lock_
\* Parameter Lock of procedure unlock at line 47 col 22 changed to Lock_u
\* Parameter Lock of procedure flush at line 64 col 21 changed to Lock_f
\* Parameter Lock of procedure try_acquire at line 89 col 27 changed to Lock_t
\* Parameter Stack of procedure push at line 111 col 20 changed to Stack_
\* Parameter Node of procedure push at line 111 col 27 changed to Node_
\* Parameter Node of procedure wait at line 132 col 20 changed to Node_w
CONSTANT defaultInitValue
VARIABLES Locks, rVal, Nodes, pc, stack

(* define statement *)
NULL == 0
NUM_LOCKS == 1
L == 1

VARIABLES Lock_, Lock_u, Lock_f, Lock_t, Lock, Stack_, Node_, Stack, Node_w, 
          Node

vars == << Locks, rVal, Nodes, pc, stack, Lock_, Lock_u, Lock_f, Lock_t, Lock, 
           Stack_, Node_, Stack, Node_w, Node >>

ProcSet == (1..NUM_PROCESSES)

Init == (* Global variables *)
        /\ Locks =     [
                   Stack |-> [ LockId \in 1..NUM_LOCKS |-> <<>> ],
                   Lock |-> [ LockId \in 1..NUM_LOCKS |-> FALSE ]
                   ]
        /\ rVal = [ Id \in 1..NUM_PROCESSES |-> defaultInitValue ]
        /\ Nodes = [ Id \in 1..NUM_PROCESSES |-> defaultInitValue ]
        (* Procedure lock *)
        /\ Lock_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure unlock *)
        /\ Lock_u = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure flush *)
        /\ Lock_f = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure try_acquire *)
        /\ Lock_t = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure release *)
        /\ Lock = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure push *)
        /\ Stack_ = [ self \in ProcSet |-> defaultInitValue]
        /\ Node_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure pop *)
        /\ Stack = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wait *)
        /\ Node_w = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure signal *)
        /\ Node = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "LOCK"]

PUSH_NODE(self) == /\ pc[self] = "PUSH_NODE"
                   /\ IF SHOULD_LOG
                         THEN /\ PrintT(<<self, Head(stack[self])["procedure"]>> \o (<<>>))
                         ELSE /\ TRUE
                   /\ Nodes' = [Nodes EXCEPT ![self] = FALSE]
                   /\ /\ Node_' = [Node_ EXCEPT ![self] = self]
                      /\ Stack_' = [Stack_ EXCEPT ![self] = Lock_[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "push",
                                                               pc        |->  "FLUSH_LOCK_",
                                                               Stack_    |->  Stack_[self],
                                                               Node_     |->  Node_[self] ] >>
                                                           \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "A_p"]
                   /\ UNCHANGED << Locks, rVal, Lock_, Lock_u, Lock_f, Lock_t, 
                                   Lock, Stack, Node_w, Node >>

FLUSH_LOCK_(self) == /\ pc[self] = "FLUSH_LOCK_"
                     /\ /\ Lock_f' = [Lock_f EXCEPT ![self] = Lock_[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flush",
                                                                 pc        |->  "WAIT",
                                                                 Lock_f    |->  Lock_f[self] ] >>
                                                             \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "DEBUG"]
                     /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_t, 
                                     Lock, Stack_, Node_, Stack, Node_w, Node >>

WAIT(self) == /\ pc[self] = "WAIT"
              /\ /\ Node_w' = [Node_w EXCEPT ![self] = self]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wait",
                                                          pc        |->  Head(stack[self]).pc,
                                                          Node_w    |->  Node_w[self] ] >>
                                                      \o Tail(stack[self])]
              /\ pc' = [pc EXCEPT ![self] = "A_w"]
              /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_f, 
                              Lock_t, Lock, Stack_, Node_, Stack, Node >>

lock(self) == PUSH_NODE(self) \/ FLUSH_LOCK_(self) \/ WAIT(self)

POP_(self) == /\ pc[self] = "POP_"
              /\ IF SHOULD_LOG
                    THEN /\ PrintT(<<self, Head(stack[self])["procedure"]>> \o (<<>>))
                    ELSE /\ TRUE
              /\ /\ Stack' = [Stack EXCEPT ![self] = Lock_u[self]]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pop",
                                                          pc        |->  "CHECK_POP_",
                                                          Stack     |->  Stack[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "A_po"]
              /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_f, 
                              Lock_t, Lock, Stack_, Node_, Node_w, Node >>

CHECK_POP_(self) == /\ pc[self] = "CHECK_POP_"
                    /\ IF rVal[self] /= NULL
                          THEN /\ /\ Node' = [Node EXCEPT ![self] = rVal[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "signal",
                                                                           pc        |->  Head(stack[self]).pc,
                                                                           Node      |->  Node[self] ] >>
                                                                       \o Tail(stack[self])]
                               /\ pc' = [pc EXCEPT ![self] = "A"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "RELEASE_"]
                               /\ UNCHANGED << stack, Node >>
                    /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_f, 
                                    Lock_t, Lock, Stack_, Node_, Stack, Node_w >>

RELEASE_(self) == /\ pc[self] = "RELEASE_"
                  /\ /\ Lock' = [Lock EXCEPT ![self] = Lock_u[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release",
                                                              pc        |->  "FLUSH_LOCK",
                                                              Lock      |->  Lock[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "A_r"]
                  /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_f, 
                                  Lock_t, Stack_, Node_, Stack, Node_w, Node >>

FLUSH_LOCK(self) == /\ pc[self] = "FLUSH_LOCK"
                    /\ /\ Lock_f' = [Lock_f EXCEPT ![self] = Lock_u[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flush",
                                                                pc        |->  Head(stack[self]).pc,
                                                                Lock_f    |->  Lock_f[self] ] >>
                                                            \o Tail(stack[self])]
                    /\ pc' = [pc EXCEPT ![self] = "DEBUG"]
                    /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_t, 
                                    Lock, Stack_, Node_, Stack, Node_w, Node >>

unlock(self) == POP_(self) \/ CHECK_POP_(self) \/ RELEASE_(self)
                   \/ FLUSH_LOCK(self)

DEBUG(self) == /\ pc[self] = "DEBUG"
               /\ IF SHOULD_LOG
                     THEN /\ PrintT(<<self, Head(stack[self])["procedure"]>> \o (<<>>))
                     ELSE /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "LOOP"]
               /\ UNCHANGED << Locks, rVal, Nodes, stack, Lock_, Lock_u, 
                               Lock_f, Lock_t, Lock, Stack_, Node_, Stack, 
                               Node_w, Node >>

LOOP(self) == /\ pc[self] = "LOOP"
              /\ IF Locks.Stack[Lock_f[self]] /= <<>>
                    THEN /\ pc' = [pc EXCEPT ![self] = "TRY_ACQUIRE"]
                         /\ UNCHANGED << stack, Lock_f >>
                    ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ Lock_f' = [Lock_f EXCEPT ![self] = Head(stack[self]).Lock_f]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_t, Lock, 
                              Stack_, Node_, Stack, Node_w, Node >>

TRY_ACQUIRE(self) == /\ pc[self] = "TRY_ACQUIRE"
                     /\ /\ Lock_t' = [Lock_t EXCEPT ![self] = Lock_f[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "try_acquire",
                                                                 pc        |->  "CHECK_ACQUIRE",
                                                                 Lock_t    |->  Lock_t[self] ] >>
                                                             \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "A_"]
                     /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_f, 
                                     Lock, Stack_, Node_, Stack, Node_w, Node >>

CHECK_ACQUIRE(self) == /\ pc[self] = "CHECK_ACQUIRE"
                       /\ IF ~rVal[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ Lock_f' = [Lock_f EXCEPT ![self] = Head(stack[self]).Lock_f]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "POP"]
                                  /\ UNCHANGED << stack, Lock_f >>
                       /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, 
                                       Lock_t, Lock, Stack_, Node_, Stack, 
                                       Node_w, Node >>

POP(self) == /\ pc[self] = "POP"
             /\ /\ Stack' = [Stack EXCEPT ![self] = Lock_f[self]]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pop",
                                                         pc        |->  "CHECK_POP",
                                                         Stack     |->  Stack[self] ] >>
                                                     \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "A_po"]
             /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_f, Lock_t, 
                             Lock, Stack_, Node_, Node_w, Node >>

CHECK_POP(self) == /\ pc[self] = "CHECK_POP"
                   /\ IF rVal[self]/= NULL
                         THEN /\ /\ Node' = [Node EXCEPT ![self] = rVal[self]]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "signal",
                                                                          pc        |->  Head(stack[self]).pc,
                                                                          Node      |->  Node[self] ] >>
                                                                      \o Tail(stack[self])]
                              /\ pc' = [pc EXCEPT ![self] = "A"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "RELEASE"]
                              /\ UNCHANGED << stack, Node >>
                   /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_f, 
                                   Lock_t, Lock, Stack_, Node_, Stack, Node_w >>

RELEASE(self) == /\ pc[self] = "RELEASE"
                 /\ /\ Lock' = [Lock EXCEPT ![self] = Lock_f[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release",
                                                             pc        |->  "LOOP",
                                                             Lock      |->  Lock[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "A_r"]
                 /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_u, Lock_f, 
                                 Lock_t, Stack_, Node_, Stack, Node_w, Node >>

flush(self) == DEBUG(self) \/ LOOP(self) \/ TRY_ACQUIRE(self)
                  \/ CHECK_ACQUIRE(self) \/ POP(self) \/ CHECK_POP(self)
                  \/ RELEASE(self)

A_(self) == /\ pc[self] = "A_"
            /\ IF SHOULD_LOG
                  THEN /\ PrintT(<<self, Head(stack[self])["procedure"]>> \o (<<Locks.Lock[Lock_t[self]]>>))
                  ELSE /\ TRUE
            /\ IF Locks.Lock[Lock_t[self]]
                  THEN /\ rVal' = [rVal EXCEPT ![self] = FALSE]
                       /\ Locks' = Locks
                  ELSE /\ Locks' = [Locks EXCEPT !.Lock[Lock_t[self]] = TRUE]
                       /\ rVal' = [rVal EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ Lock_t' = [Lock_t EXCEPT ![self] = Head(stack[self]).Lock_t]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << Nodes, Lock_, Lock_u, Lock_f, Lock, Stack_, Node_, 
                            Stack, Node_w, Node >>

try_acquire(self) == A_(self)

A_r(self) == /\ pc[self] = "A_r"
             /\ IF SHOULD_LOG
                   THEN /\ PrintT(<<self, Head(stack[self])["procedure"]>> \o (<<>>))
                   ELSE /\ TRUE
             /\ Assert(Locks.Lock[Lock[self]], 
                       "Failure of assertion at line 106, column 13.")
             /\ Locks' = [Locks EXCEPT !.Lock[Lock[self]] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ Lock' = [Lock EXCEPT ![self] = Head(stack[self]).Lock]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << rVal, Nodes, Lock_, Lock_u, Lock_f, Lock_t, 
                             Stack_, Node_, Stack, Node_w, Node >>

release(self) == A_r(self)

A_p(self) == /\ pc[self] = "A_p"
             /\ IF SHOULD_LOG
                   THEN /\ PrintT(<<self, Head(stack[self])["procedure"]>> \o (<<>>))
                   ELSE /\ TRUE
             /\ Locks' = [Locks EXCEPT !.Stack[Stack_[self]] = <<Node_[self]>> \o Locks.Stack[Stack_[self]]]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ Stack_' = [Stack_ EXCEPT ![self] = Head(stack[self]).Stack_]
             /\ Node_' = [Node_ EXCEPT ![self] = Head(stack[self]).Node_]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << rVal, Nodes, Lock_, Lock_u, Lock_f, Lock_t, Lock, 
                             Stack, Node_w, Node >>

push(self) == A_p(self)

A_po(self) == /\ pc[self] = "A_po"
              /\ IF SHOULD_LOG
                    THEN /\ PrintT(<<self, Head(stack[self])["procedure"]>> \o (<<>>))
                    ELSE /\ TRUE
              /\ IF Locks.Stack[Stack[self]] = <<>>
                    THEN /\ rVal' = [rVal EXCEPT ![self] = NULL]
                         /\ Locks' = Locks
                    ELSE /\ rVal' = [rVal EXCEPT ![self] = Head(Locks.Stack[Stack[self]])]
                         /\ Locks' = [Locks EXCEPT !.Stack[Stack[self]] = Tail(Locks.Stack[Stack[self]])]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ Stack' = [Stack EXCEPT ![self] = Head(stack[self]).Stack]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Nodes, Lock_, Lock_u, Lock_f, Lock_t, Lock, 
                              Stack_, Node_, Node_w, Node >>

pop(self) == A_po(self)

A_w(self) == /\ pc[self] = "A_w"
             /\ IF SHOULD_LOG
                   THEN /\ PrintT(<<self, Head(stack[self])["procedure"]>> \o (<<>>))
                   ELSE /\ TRUE
             /\ Nodes[self]
             /\ Nodes' = [Nodes EXCEPT ![self] = NULL]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ Node_w' = [Node_w EXCEPT ![self] = Head(stack[self]).Node_w]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Locks, rVal, Lock_, Lock_u, Lock_f, Lock_t, Lock, 
                             Stack_, Node_, Stack, Node >>

wait(self) == A_w(self)

A(self) == /\ pc[self] = "A"
           /\ IF SHOULD_LOG
                 THEN /\ PrintT(<<self, Head(stack[self])["procedure"]>> \o (<<>>))
                 ELSE /\ TRUE
           /\ Assert(Nodes[Node[self]] = FALSE, 
                     "Failure of assertion at line 145, column 13.")
           /\ Nodes' = [Nodes EXCEPT ![Node[self]] = TRUE]
           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
           /\ Node' = [Node EXCEPT ![self] = Head(stack[self]).Node]
           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
           /\ UNCHANGED << Locks, rVal, Lock_, Lock_u, Lock_f, Lock_t, Lock, 
                           Stack_, Node_, Stack, Node_w >>

signal(self) == A(self)

LOCK(self) == /\ pc[self] = "LOCK"
              /\ IF SHOULD_LOG
                    THEN /\ PrintT(<<self, "start">>)
                    ELSE /\ TRUE
              /\ /\ Lock_' = [Lock_ EXCEPT ![self] = L]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                          pc        |->  "CS",
                                                          Lock_     |->  Lock_[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "PUSH_NODE"]
              /\ UNCHANGED << Locks, rVal, Nodes, Lock_u, Lock_f, Lock_t, Lock, 
                              Stack_, Node_, Stack, Node_w, Node >>

CS(self) == /\ pc[self] = "CS"
            /\ Assert(\A i \in 1..NUM_PROCESSES : (i = self) <=> (pc[i] = "CS"), 
                      "Failure of assertion at line 156, column 13.")
            /\ pc' = [pc EXCEPT ![self] = "UNLOCK"]
            /\ UNCHANGED << Locks, rVal, Nodes, stack, Lock_, Lock_u, Lock_f, 
                            Lock_t, Lock, Stack_, Node_, Stack, Node_w, Node >>

UNLOCK(self) == /\ pc[self] = "UNLOCK"
                /\ /\ Lock_u' = [Lock_u EXCEPT ![self] = L]
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                            pc        |->  "DEBUG_END",
                                                            Lock_u    |->  Lock_u[self] ] >>
                                                        \o stack[self]]
                /\ pc' = [pc EXCEPT ![self] = "POP_"]
                /\ UNCHANGED << Locks, rVal, Nodes, Lock_, Lock_f, Lock_t, 
                                Lock, Stack_, Node_, Stack, Node_w, Node >>

DEBUG_END(self) == /\ pc[self] = "DEBUG_END"
                   /\ IF SHOULD_LOG
                         THEN /\ PrintT(<<self, "finish">>)
                         ELSE /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << Locks, rVal, Nodes, stack, Lock_, Lock_u, 
                                   Lock_f, Lock_t, Lock, Stack_, Node_, Stack, 
                                   Node_w, Node >>

p(self) == LOCK(self) \/ CS(self) \/ UNLOCK(self) \/ DEBUG_END(self)

Next == (\E self \in ProcSet:  \/ lock(self) \/ unlock(self) \/ flush(self)
                               \/ try_acquire(self) \/ release(self)
                               \/ push(self) \/ pop(self) \/ wait(self)
                               \/ signal(self))
           \/ (\E self \in 1..NUM_PROCESSES: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in 1..NUM_PROCESSES : /\ SF_vars(p(self))
                                          /\ SF_vars(lock(self))
                                          /\ SF_vars(unlock(self))
                                          /\ SF_vars(flush(self))
                                          /\ SF_vars(try_acquire(self))
                                          /\ SF_vars(release(self))
                                          /\ SF_vars(push(self))
                                          /\ SF_vars(pop(self))
                                          /\ SF_vars(wait(self))
                                          /\ SF_vars(signal(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
