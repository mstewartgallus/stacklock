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
    
    macro swap(Lhs, New_Value, Result) begin
        Result := Lhs;
        Lhs := New_Value;
    end macro;

    procedure lock()
        variables Tmp;
    begin
    CHECK:
        if UNLOCKED = Lock then
            Lock := LOCKED;
            return;
        elsif LOCKED = Lock then
\* This is a test-and-test and set lock and so this needs to be a separate step.
        SWAP:
            swap(Lock, LOCKED_WITH_WAITERS, Tmp);
\* Tmp does not get assigned until the next step.
        RET:
            if UNLOCKED = Tmp then
                return;
            end if;
        end if;
    LOOP:
        while TRUE do
        CHECK2:
            if Lock /= LOCKED_WITH_WAITERS then
\* This is a test-and-test and set lock and so this needs to be a separate step.
            SWAP2:
                swap(Lock, LOCKED_WITH_WAITERS, Tmp);            
\* Tmp does not get assigned until the next step.
            RET2:
                if UNLOCKED = Tmp then
                    return;
                end if;
            end if;
        FUTEX_WAIT:
            await Semaphore;
            Semaphore := FALSE;
        end while;
    end procedure;
    
    procedure unlock()
        variables Tmp;
    begin
    SWAP:
        swap(Lock, UNLOCKED, Tmp);
    CHECK:
        if Tmp = LOCKED_WITH_WAITERS then
            Semaphore := TRUE;
        end if;
        return;
    end procedure
    
    fair process p \in 1..NUM_PROCESSES
        variables Counter = 0;
    begin
    LOOP:
        while Counter < NUM_LOOPS do
        LOCK:
            call lock();
\* Assert the critical section is only reachable by one process at at time.
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
\* Label CHECK of procedure lock at line 28 col 9 changed to CHECK_
\* Label SWAP of procedure lock at line 20 col 9 changed to SWAP_
\* Label LOOP of procedure lock at line 42 col 9 changed to LOOP_
\* Procedure variable Tmp of procedure lock at line 25 col 19 changed to Tmp_
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

CHECK_(self) == /\ pc[self] = "CHECK_"
                /\ IF UNLOCKED = Lock
                      THEN /\ Lock' = LOCKED
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ Tmp_' = [Tmp_ EXCEPT ![self] = Head(stack[self]).Tmp_]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      ELSE /\ IF LOCKED = Lock
                                 THEN /\ pc' = [pc EXCEPT ![self] = "SWAP_"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "LOOP_"]
                           /\ UNCHANGED << Lock, stack, Tmp_ >>
                /\ UNCHANGED << Semaphore, Nodes, Tmp, Counter >>

SWAP_(self) == /\ pc[self] = "SWAP_"
               /\ Tmp_' = [Tmp_ EXCEPT ![self] = Lock]
               /\ Lock' = LOCKED_WITH_WAITERS
               /\ pc' = [pc EXCEPT ![self] = "RET"]
               /\ UNCHANGED << Semaphore, Nodes, stack, Tmp, Counter >>

RET(self) == /\ pc[self] = "RET"
             /\ IF UNLOCKED = Tmp_[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ Tmp_' = [Tmp_ EXCEPT ![self] = Head(stack[self]).Tmp_]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "LOOP_"]
                        /\ UNCHANGED << stack, Tmp_ >>
             /\ UNCHANGED << Lock, Semaphore, Nodes, Tmp, Counter >>

LOOP_(self) == /\ pc[self] = "LOOP_"
               /\ pc' = [pc EXCEPT ![self] = "CHECK2"]
               /\ UNCHANGED << Lock, Semaphore, Nodes, stack, Tmp_, Tmp, 
                               Counter >>

CHECK2(self) == /\ pc[self] = "CHECK2"
                /\ IF Lock /= LOCKED_WITH_WAITERS
                      THEN /\ pc' = [pc EXCEPT ![self] = "SWAP2"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "FUTEX_WAIT"]
                /\ UNCHANGED << Lock, Semaphore, Nodes, stack, Tmp_, Tmp, 
                                Counter >>

SWAP2(self) == /\ pc[self] = "SWAP2"
               /\ Tmp_' = [Tmp_ EXCEPT ![self] = Lock]
               /\ Lock' = LOCKED_WITH_WAITERS
               /\ pc' = [pc EXCEPT ![self] = "RET2"]
               /\ UNCHANGED << Semaphore, Nodes, stack, Tmp, Counter >>

RET2(self) == /\ pc[self] = "RET2"
              /\ IF UNLOCKED = Tmp_[self]
                    THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ Tmp_' = [Tmp_ EXCEPT ![self] = Head(stack[self]).Tmp_]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "FUTEX_WAIT"]
                         /\ UNCHANGED << stack, Tmp_ >>
              /\ UNCHANGED << Lock, Semaphore, Nodes, Tmp, Counter >>

FUTEX_WAIT(self) == /\ pc[self] = "FUTEX_WAIT"
                    /\ Semaphore
                    /\ Semaphore' = FALSE
                    /\ pc' = [pc EXCEPT ![self] = "LOOP_"]
                    /\ UNCHANGED << Lock, Nodes, stack, Tmp_, Tmp, Counter >>

lock(self) == CHECK_(self) \/ SWAP_(self) \/ RET(self) \/ LOOP_(self)
                 \/ CHECK2(self) \/ SWAP2(self) \/ RET2(self)
                 \/ FUTEX_WAIT(self)

SWAP(self) == /\ pc[self] = "SWAP"
              /\ Tmp' = [Tmp EXCEPT ![self] = Lock]
              /\ Lock' = UNLOCKED
              /\ pc' = [pc EXCEPT ![self] = "CHECK"]
              /\ UNCHANGED << Semaphore, Nodes, stack, Tmp_, Counter >>

CHECK(self) == /\ pc[self] = "CHECK"
               /\ IF Tmp[self] = LOCKED_WITH_WAITERS
                     THEN /\ Semaphore' = TRUE
                     ELSE /\ TRUE
                          /\ UNCHANGED Semaphore
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ Tmp' = [Tmp EXCEPT ![self] = Head(stack[self]).Tmp]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Lock, Nodes, Tmp_, Counter >>

unlock(self) == SWAP(self) \/ CHECK(self)

LOOP(self) == /\ pc[self] = "LOOP"
              /\ IF Counter[self] < NUM_LOOPS
                    THEN /\ pc' = [pc EXCEPT ![self] = "LOCK"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << Lock, Semaphore, Nodes, stack, Tmp_, Tmp, 
                              Counter >>

LOCK(self) == /\ pc[self] = "LOCK"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                       pc        |->  "CS",
                                                       Tmp_      |->  Tmp_[self] ] >>
                                                   \o stack[self]]
              /\ Tmp_' = [Tmp_ EXCEPT ![self] = defaultInitValue]
              /\ pc' = [pc EXCEPT ![self] = "CHECK_"]
              /\ UNCHANGED << Lock, Semaphore, Nodes, Tmp, Counter >>

CS(self) == /\ pc[self] = "CS"
            /\ Assert(\A i \in 1..NUM_PROCESSES : (i = self) <=> (pc[i] = "CS"), 
                      "Failure of assertion at line 81, column 13.")
            /\ pc' = [pc EXCEPT ![self] = "UNLOCK"]
            /\ UNCHANGED << Lock, Semaphore, Nodes, stack, Tmp_, Tmp, Counter >>

UNLOCK(self) == /\ pc[self] = "UNLOCK"
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                         pc        |->  "COUNT",
                                                         Tmp       |->  Tmp[self] ] >>
                                                     \o stack[self]]
                /\ Tmp' = [Tmp EXCEPT ![self] = defaultInitValue]
                /\ pc' = [pc EXCEPT ![self] = "SWAP"]
                /\ UNCHANGED << Lock, Semaphore, Nodes, Tmp_, Counter >>

COUNT(self) == /\ pc[self] = "COUNT"
               /\ Counter' = [Counter EXCEPT ![self] = Counter[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "LOOP"]
               /\ UNCHANGED << Lock, Semaphore, Nodes, stack, Tmp_, Tmp >>

p(self) == LOOP(self) \/ LOCK(self) \/ CS(self) \/ UNLOCK(self)
              \/ COUNT(self)

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
