------------------------------ MODULE TTSLock ------------------------------
EXTENDS Naturals, TLC, Sequences

CONSTANT NUM_PROCESSES
CONSTANT NUM_LOOPS

(*--fair algorithm lockAlg
    variables
        Lock = UNLOCKED,
        Semaphore = FALSE,
        Nodes = [ self \in ProcSet |-> defaultInitValue ];

    define
        UNLOCKED == 0
        LOCKED == 1
        LOCKED_WITH_WAITERS == 2
    end define;

    procedure lock()
        variables Tmp;
    begin
    CHECK:
        if UNLOCKED = Lock then
            Lock := LOCKED;
            return;
        elsif LOCKED = Lock then
        SWAP:
            Tmp := Lock;
            Lock := LOCKED_WITH_WAITERS;
            if UNLOCKED = Tmp then
            RET:
                return;
            end if;
        end if;
    LOOP:
        while TRUE do
        ACQUIRE:
            Tmp := Lock;
            Lock := LOCKED_WITH_WAITERS;
            if Tmp = UNLOCKED then
            RET2:
                return;
            end if;
        FUTEX_WAIT:
            await Semaphore;
            Semaphore := FALSE;
        end while;
    end procedure;
    
    procedure unlock()
        variables Tmp;
    begin
    DEC:
        Tmp := Lock;
        Lock := UNLOCKED;
        if Tmp = LOCKED_WITH_WAITERS then
        UNLOCK:
            Semaphore := TRUE;
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
\* Label RET of procedure lock at line 32 col 17 changed to RET_
\* Label LOOP of procedure lock at line 36 col 9 changed to LOOP_
\* Label UNLOCK of procedure unlock at line 58 col 13 changed to UNLOCK_
\* Procedure variable Tmp of procedure lock at line 20 col 19 changed to Tmp_
CONSTANT defaultInitValue
VARIABLES Lock, Semaphore, Nodes, pc, stack

(* define statement *)
UNLOCKED == 0
LOCKED == 1
LOCKED_WITH_WAITERS == 2

VARIABLES Tmp_, Tmp, Counter

vars == << Lock, Semaphore, Nodes, pc, stack, Tmp_, Tmp, Counter >>

ProcSet == (1..NUM_PROCESSES)

Init == (* Global variables *)
        /\ Lock = UNLOCKED
        /\ Semaphore = FALSE
        /\ Nodes = [ self \in ProcSet |-> defaultInitValue ]
        (* Procedure lock *)
        /\ Tmp_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure unlock *)
        /\ Tmp = [ self \in ProcSet |-> defaultInitValue]
        (* Process p *)
        /\ Counter = [self \in 1..NUM_PROCESSES |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "LOOP"]

CHECK(self) == /\ pc[self] = "CHECK"
               /\ IF UNLOCKED = Lock
                     THEN /\ Lock' = LOCKED
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ Tmp_' = [Tmp_ EXCEPT ![self] = Head(stack[self]).Tmp_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     ELSE /\ IF LOCKED = Lock
                                THEN /\ pc' = [pc EXCEPT ![self] = "SWAP"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "LOOP_"]
                          /\ UNCHANGED << Lock, stack, Tmp_ >>
               /\ UNCHANGED << Semaphore, Nodes, Tmp, Counter >>

SWAP(self) == /\ pc[self] = "SWAP"
              /\ Tmp_' = [Tmp_ EXCEPT ![self] = Lock]
              /\ Lock' = LOCKED_WITH_WAITERS
              /\ IF UNLOCKED = Tmp_'[self]
                    THEN /\ pc' = [pc EXCEPT ![self] = "RET_"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "LOOP_"]
              /\ UNCHANGED << Semaphore, Nodes, stack, Tmp, Counter >>

RET_(self) == /\ pc[self] = "RET_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ Tmp_' = [Tmp_ EXCEPT ![self] = Head(stack[self]).Tmp_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Lock, Semaphore, Nodes, Tmp, Counter >>

LOOP_(self) == /\ pc[self] = "LOOP_"
               /\ pc' = [pc EXCEPT ![self] = "ACQUIRE"]
               /\ UNCHANGED << Lock, Semaphore, Nodes, stack, Tmp_, Tmp, 
                               Counter >>

ACQUIRE(self) == /\ pc[self] = "ACQUIRE"
                 /\ Tmp_' = [Tmp_ EXCEPT ![self] = Lock]
                 /\ Lock' = LOCKED_WITH_WAITERS
                 /\ IF Tmp_'[self] = UNLOCKED
                       THEN /\ pc' = [pc EXCEPT ![self] = "RET2"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "FUTEX_WAIT"]
                 /\ UNCHANGED << Semaphore, Nodes, stack, Tmp, Counter >>

RET2(self) == /\ pc[self] = "RET2"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ Tmp_' = [Tmp_ EXCEPT ![self] = Head(stack[self]).Tmp_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Lock, Semaphore, Nodes, Tmp, Counter >>

FUTEX_WAIT(self) == /\ pc[self] = "FUTEX_WAIT"
                    /\ Semaphore
                    /\ Semaphore' = FALSE
                    /\ pc' = [pc EXCEPT ![self] = "LOOP_"]
                    /\ UNCHANGED << Lock, Nodes, stack, Tmp_, Tmp, Counter >>

lock(self) == CHECK(self) \/ SWAP(self) \/ RET_(self) \/ LOOP_(self)
                 \/ ACQUIRE(self) \/ RET2(self) \/ FUTEX_WAIT(self)

DEC(self) == /\ pc[self] = "DEC"
             /\ Tmp' = [Tmp EXCEPT ![self] = Lock]
             /\ Lock' = UNLOCKED
             /\ IF Tmp'[self] = LOCKED_WITH_WAITERS
                   THEN /\ pc' = [pc EXCEPT ![self] = "UNLOCK_"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "RET"]
             /\ UNCHANGED << Semaphore, Nodes, stack, Tmp_, Counter >>

UNLOCK_(self) == /\ pc[self] = "UNLOCK_"
                 /\ Semaphore' = TRUE
                 /\ pc' = [pc EXCEPT ![self] = "RET"]
                 /\ UNCHANGED << Lock, Nodes, stack, Tmp_, Tmp, Counter >>

RET(self) == /\ pc[self] = "RET"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ Tmp' = [Tmp EXCEPT ![self] = Head(stack[self]).Tmp]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << Lock, Semaphore, Nodes, Tmp_, Counter >>

unlock(self) == DEC(self) \/ UNLOCK_(self) \/ RET(self)

LOOP(self) == /\ pc[self] = "LOOP"
              /\ IF Counter[self] < NUM_LOOPS
                    THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                                  pc        |->  "CS",
                                                                  Tmp_      |->  Tmp_[self] ] >>
                                                              \o stack[self]]
                         /\ Tmp_' = [Tmp_ EXCEPT ![self] = defaultInitValue]
                         /\ pc' = [pc EXCEPT ![self] = "CHECK"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << stack, Tmp_ >>
              /\ UNCHANGED << Lock, Semaphore, Nodes, Tmp, Counter >>

CS(self) == /\ pc[self] = "CS"
            /\ Assert(\A i \in 1..NUM_PROCESSES : (i = self) <=> (pc[i] = "CS"), 
                      "Failure of assertion at line 71, column 13.")
            /\ pc' = [pc EXCEPT ![self] = "UNLOCK"]
            /\ UNCHANGED << Lock, Semaphore, Nodes, stack, Tmp_, Tmp, Counter >>

UNLOCK(self) == /\ pc[self] = "UNLOCK"
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                         pc        |->  "COUNT",
                                                         Tmp       |->  Tmp[self] ] >>
                                                     \o stack[self]]
                /\ Tmp' = [Tmp EXCEPT ![self] = defaultInitValue]
                /\ pc' = [pc EXCEPT ![self] = "DEC"]
                /\ UNCHANGED << Lock, Semaphore, Nodes, Tmp_, Counter >>

COUNT(self) == /\ pc[self] = "COUNT"
               /\ Counter' = [Counter EXCEPT ![self] = Counter[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "LOOP"]
               /\ UNCHANGED << Lock, Semaphore, Nodes, stack, Tmp_, Tmp >>

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
