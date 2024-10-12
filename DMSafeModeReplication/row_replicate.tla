--------------------------- MODULE row_replicate ---------------------------
EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANT Values
ASSUME Cardinality(Values) > 0
CONSTANT NumChanges
ASSUME NumChanges > 0
CONSTANT NumColumns
ASSUME NumColumns > 0

CONSTANT Null

\* assuming all columns have UNIQUE constraint, and we call the first column "PK"
Columns == 1..NumColumns

ChangeType == {"insert", "update", "delete"}
RowType == [Columns -> Values]
RowChangeType == [type: ChangeType, old: RowType \union {Null}, new: RowType \union {Null}]

(* --algorithm generate_change_log
variables
  round = 0;
  upstream = {};
  downstream = {};
  change_log = <<>>;
  log_index = 1;

define
  TypeInvariant ==
    /\ round >= 0
    /\ upstream \subseteq RowType
    /\ downstream \subseteq RowType
    /\ \A i \in DOMAIN change_log: i > 0 /\ change_log[i] \in RowChangeType
    /\ log_index > 0
    
  AllColumnsUniqueInvariant ==
    \A i \in Columns:
      /\ Cardinality({row[i]: row \in upstream}) = Cardinality(upstream) 
      /\ Cardinality({row[i]: row \in downstream}) = Cardinality(downstream) 
  
  IsRowValid(row, rows) ==
    \A col \in Columns: \A r \in rows: row[col] # r[col]
    
  ValidNewRows(current_rows) ==
    {r \in RowType: IsRowValid(r, current_rows)}
  
  Insert(rows, new_row) ==
    rows \union {new_row}
  
  Update(rows, old_row, new_row) ==
    IF old_row \notin rows THEN rows ELSE ((rows \ {old_row}) \union {new_row})
      
  Delete(rows, old_row) ==
    rows \ {old_row}
  
  DeleteByPK(rows, old_row) ==
    {x \in rows: x[1] # old_row[1]}
  
  UpdateByPK(rows, old_row, new_row) ==
    IF old_row[1] \notin {x[1]: x \in rows} THEN rows ELSE Insert(DeleteByPK(rows, old_row), new_row)
  
  Replace(rows, new_row) ==
    Insert({x \in rows: \A col \in Columns: x[col] # new_row[col]}, new_row)
  
  InsertIgnore(rows, new_row) ==
    IF \E x \in rows: \E col \in Columns: x[col] = new_row[col] THEN rows ELSE Insert(rows, new_row)

  DataCorrectness == pc = "Done" => upstream = downstream
    
end define; 

begin
  ChangeUpstream:
    while round <= NumChanges do
      either
        \* try to insert a row
        with new_row \in ValidNewRows(upstream) do
          upstream := upstream \union {new_row};
          change_log := Append(change_log, [type |-> "insert", old |-> Null, new |-> new_row]);
        end with;
      or
        \* try to delete a row
        with old_row \in upstream do
          upstream := upstream \ {old_row};
          change_log := Append(change_log, [type |-> "delete", old |-> old_row, new |-> Null]);
        end with;
      or
        \* try to update a row
        with old_row \in upstream do
          with new_row \in ValidNewRows(upstream \ {old_row}) do
            \* for simplicity we allow update to same value
            upstream := (upstream \ {old_row}) \union {new_row};
            change_log := Append(change_log, [type |-> "update", old |-> old_row, new |-> new_row]);
          end with;
        end with;
      end either;
      
      round := round + 1;
    end while;

\*   Replicate:
\*     while log_index <= Len(change_log) do
\*       with change = change_log[log_index] do
\*         if change.type = "insert" then
\*           downstream := Insert(downstream, change.new)
\*         elsif change.type = "delete" then
\*           downstream := DeleteByPK(downstream, change.old)
\*         else
\*           downstream := UpdateByPK(downstream, change.old, change.new)
\*         end if;
\*       end with;

\*       log_index := log_index + 1;
\*     end while;

  SafeModeReplicate:
    while log_index <= Len(change_log) do
      with change = change_log[log_index] do
        if change.type = "insert" then
          downstream := InsertIgnore(downstream, change.new)
        elsif change.type = "delete" then
          downstream := DeleteByPK(downstream, change.old)
        else
          downstream := InsertIgnore(DeleteByPK(downstream, change.old), change.new)
        end if;
      end with;

      with index \in 1..(log_index + 1) do
        log_index := index;
      end with;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7ef21de3" /\ chksum(tla) = "768aeffe")
VARIABLES round, upstream, downstream, change_log, log_index, pc

(* define statement *)
TypeInvariant ==
  /\ round >= 0
  /\ upstream \subseteq RowType
  /\ downstream \subseteq RowType
  /\ \A i \in DOMAIN change_log: i > 0 /\ change_log[i] \in RowChangeType
  /\ log_index > 0

AllColumnsUniqueInvariant ==
  \A i \in Columns:
    /\ Cardinality({row[i]: row \in upstream}) = Cardinality(upstream)
    /\ Cardinality({row[i]: row \in downstream}) = Cardinality(downstream)

IsRowValid(row, rows) ==
  \A col \in Columns: \A r \in rows: row[col] # r[col]

ValidNewRows(current_rows) ==
  {r \in RowType: IsRowValid(r, current_rows)}

Insert(rows, new_row) ==
  rows \union {new_row}

Update(rows, old_row, new_row) ==
  IF old_row \notin rows THEN rows ELSE ((rows \ {old_row}) \union {new_row})

Delete(rows, old_row) ==
  rows \ {old_row}

DeleteByPK(rows, old_row) ==
  {x \in rows: x[1] # old_row[1]}

UpdateByPK(rows, old_row, new_row) ==
  IF old_row[1] \notin {x[1]: x \in rows} THEN rows ELSE Insert(DeleteByPK(rows, old_row), new_row)

Replace(rows, new_row) ==
  Insert({x \in rows: \A col \in Columns: x[col] # new_row[col]}, new_row)

InsertIgnore(rows, new_row) ==
  IF \E x \in rows: \E col \in Columns: x[col] = new_row[col] THEN rows ELSE Insert(rows, new_row)

DataCorrectness == pc = "Done" => upstream = downstream


vars == << round, upstream, downstream, change_log, log_index, pc >>

Init == (* Global variables *)
        /\ round = 0
        /\ upstream = {}
        /\ downstream = {}
        /\ change_log = <<>>
        /\ log_index = 1
        /\ pc = "ChangeUpstream"

ChangeUpstream == /\ pc = "ChangeUpstream"
                  /\ IF round <= NumChanges
                        THEN /\ \/ /\ \E new_row \in ValidNewRows(upstream):
                                        /\ upstream' = (upstream \union {new_row})
                                        /\ change_log' = Append(change_log, [type |-> "insert", old |-> Null, new |-> new_row])
                                \/ /\ \E old_row \in upstream:
                                        /\ upstream' = upstream \ {old_row}
                                        /\ change_log' = Append(change_log, [type |-> "delete", old |-> old_row, new |-> Null])
                                \/ /\ \E old_row \in upstream:
                                        \E new_row \in ValidNewRows(upstream \ {old_row}):
                                          /\ upstream' = ((upstream \ {old_row}) \union {new_row})
                                          /\ change_log' = Append(change_log, [type |-> "update", old |-> old_row, new |-> new_row])
                             /\ round' = round + 1
                             /\ pc' = "ChangeUpstream"
                        ELSE /\ pc' = "SafeModeReplicate"
                             /\ UNCHANGED << round, upstream, change_log >>
                  /\ UNCHANGED << downstream, log_index >>

SafeModeReplicate == /\ pc = "SafeModeReplicate"
                     /\ IF log_index <= Len(change_log)
                           THEN /\ LET change == change_log[log_index] IN
                                     IF change.type = "insert"
                                        THEN /\ downstream' = InsertIgnore(downstream, change.new)
                                        ELSE /\ IF change.type = "delete"
                                                   THEN /\ downstream' = DeleteByPK(downstream, change.old)
                                                   ELSE /\ downstream' = InsertIgnore(DeleteByPK(downstream, change.old), change.new)
                                /\ \E index \in 1..(log_index + 1):
                                     log_index' = index
                                /\ pc' = "SafeModeReplicate"
                           ELSE /\ pc' = "Done"
                                /\ UNCHANGED << downstream, log_index >>
                     /\ UNCHANGED << round, upstream, change_log >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == ChangeUpstream \/ SafeModeReplicate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Aug 27 21:31:33 CST 2022 by lance6716
\* Created Thu Aug 25 16:02:35 CST 2022 by lance6716
