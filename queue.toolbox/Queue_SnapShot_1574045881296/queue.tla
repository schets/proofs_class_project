------------------------------- MODULE queue -------------------------------
EXTENDS Integers

BufSize == 4

(* --algorithm example
variables buffer = [i \in 1..BufSize |-> -1], write_ind = 1, read_ind = 1, last_read = 0

\* CanReadUninitialized == 

fair process writer = 0
begin
 Write:
  while write_ind <= BufSize do
    \* this must come first, write before updating index
    buffer[write_ind] := write_ind;
    write_ind := write_ind + 1;
  end while;
  
end process;

fair process reader = 1
begin
 Read:
  while read_ind <= BufSize do
    last_read := buffer[read_ind];
    await read_ind < write_ind;

    \* check must come before read
    read_ind := read_ind + 1;
  end while;
  
end process;


end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES buffer, write_ind, read_ind, last_read, pc

vars == << buffer, write_ind, read_ind, last_read, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ buffer = [i \in 1..BufSize |-> -1]
        /\ write_ind = 1
        /\ read_ind = 1
        /\ last_read = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "Write"
                                        [] self = 1 -> "Read"]

Write == /\ pc[0] = "Write"
         /\ IF write_ind <= BufSize
               THEN /\ buffer' = [buffer EXCEPT ![write_ind] = write_ind]
                    /\ write_ind' = write_ind + 1
                    /\ pc' = [pc EXCEPT ![0] = "Write"]
               ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                    /\ UNCHANGED << buffer, write_ind >>
         /\ UNCHANGED << read_ind, last_read >>

writer == Write

Read == /\ pc[1] = "Read"
        /\ IF read_ind <= BufSize
              THEN /\ last_read' = buffer[read_ind]
                   /\ read_ind < write_ind
                   /\ read_ind' = read_ind + 1
                   /\ pc' = [pc EXCEPT ![1] = "Read"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                   /\ UNCHANGED << read_ind, last_read >>
        /\ UNCHANGED << buffer, write_ind >>

reader == Read

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer \/ reader
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(writer)
        /\ WF_vars(reader)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Sun Nov 17 21:57:56 EST 2019 by samuelschetterer
\* Created Sun Nov 17 20:26:38 EST 2019 by samuelschetterer
