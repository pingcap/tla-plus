--------------------------- MODULE WriteAndVerify ---------------------------

CONSTANT CLIENTS, WITH_RO, WITH_CRASHING

VARIABLE storage, clState, clFavor

Vars == << storage, clState, clFavor >>

WVTypeOk == /\ storage \in [ CLIENTS -> { "none", "empty", "written", "written-ro", "empty-ro" } ]
            /\ clState \in [ CLIENTS -> { "begin", "precheck-done", "blank-written", 
                                          "write-check-done", "committed", "aborted", "crashed" } ]
            /\ clFavor \in [ CLIENTS -> { "read-write", "read-only" } ]

WVInit == /\ storage = [ cli \in CLIENTS |-> "none" ]
          /\ clState = [ cli \in CLIENTS |-> "begin" ]
          /\ clFavor = [ cli \in CLIENTS |-> "read-write" ]

(* Only one execution can be committed. *)
(* Once committed, the file has been written. *)
WVConsistency == /\ \A i, j \in CLIENTS : 
                    i /= j /\ storage[i] = "written" => ~storage[j] \in { "written", "written-ro" }

(* "Verify" condition: storage only contains our file or nothing. *)
Check(c) == /\ clFavor[c] = "read-write" =>
               \A f \in CLIENTS : f /= c => storage[f] = "none"
            /\ clFavor[c] = "read-only" =>
               (* No conflicting write. *)
                \A f \in CLIENTS : f /= c => ~storage[f] \in { "empty", "written" }  

Precheck(c) ==    /\ clState[c] = "begin" 
                  /\ IF Check(c) 
                     THEN clState' = [ clState EXCEPT ![c] = "precheck-done" ]
                     ELSE clState' = [ clState EXCEPT ![c] = "aborted" ]
                  /\ UNCHANGED << storage, clFavor >>

IsRO(c) == clFavor[c] = "read-only"

DoWriteBlank(c) == /\ clState[c] = "precheck-done"
                   /\ storage' = [ storage EXCEPT ![c] = IF IsRO(c) THEN "empty-ro" ELSE "empty" ]
                   
WriteBlank(c) == /\ DoWriteBlank(c)
                 /\ clState' = [ clState EXCEPT ![c] = "blank-written" ]
                 /\ UNCHANGED << clFavor >>
                 

ConflictCheck(c) == /\ clState[c] = "blank-written" 
                    /\ IF Check(c) 
                       THEN clState' = [ clState EXCEPT ![c] = "write-check-done" ]
                       ELSE clState' = [ clState EXCEPT ![c] = "aborted" ]
                    /\ UNCHANGED << storage, clFavor >>
                    
(* Delete the file when aborted. *)
RollBack(c) == /\ clState[c] = "aborted"
               /\ storage[c] /= "none"
               /\ storage' = [ storage EXCEPT ![c] = "none" ]
               /\ clState' = [ clState EXCEPT ![c] = "begin" ]
               /\ UNCHANGED << clFavor >>

DoCommit(c) == /\ clState[c] = "write-check-done"
               /\ storage' = [ storage EXCEPT ![c] = IF IsRO(c) THEN "written-ro" ELSE "written" ]
             
Commit(c) == /\ DoCommit(c)
             /\ clState' = [ clState EXCEPT ![c] = "committed" ]
             /\ UNCHANGED << clFavor >>
             
BeRO(c) == /\ clState[c] = "begin"
           /\ clFavor[c] = "read-write"
           /\ clFavor' = [ clFavor EXCEPT ![c] = "read-only" ]
           /\ UNCHANGED << clState, storage >>
           
WrittenAndCrash(c) == /\ clState' = [ clState EXCEPT ![c] = "crashed" ]
                      /\ DoWriteBlank(c) \/ DoCommit(c)
                      /\ UNCHANGED << clFavor >>
                      

WVNext == \E c \in CLIENTS: \/ Precheck(c)
                            \/ WriteBlank(c)
                            \/ ConflictCheck(c)
                            \/ RollBack(c)
                            \/ Commit(c)
                            \/ WITH_CRASHING /\ WrittenAndCrash(c)
                            \/ WITH_RO /\ BeRO(c)
                            

WVSpec == WVInit /\ [][WVNext]_Vars
                    
THEOREM WVSpec => [](WVConsistency /\ WVTypeOk)
               
=============================================================================
\* Modification History
\* Last modified Wed Dec 18 14:00:06 CST 2024 by Hillium
\* Created Sat Jun 29 10:41:34 CST 2024 by Hillium
