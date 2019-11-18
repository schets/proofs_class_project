------------------------------- MODULE queue -------------------------------
EXTENDS Integers

BufSize == 4
Writes == BufSize*3

(* --algorithm queue
variables buffer = [i \in 1..BufSize |-> -1], write_ind = BufSize, read_ind = BufSize, last_read = 0, did_proper_read = 1

fair process writer = 0
begin
 Write:
  while write_ind <= Writes do
    if read_ind + BufSize > write_ind then
        \* this must come first, write before updating index
        buffer[1 + (write_ind % BufSize)] := write_ind;
        write_ind := write_ind + 1;
    end if;
  end while;
  
end process;


fair process reader = 1
begin
 Read:
  while read_ind <= Writes do
    if read_ind < write_ind then
        last_read := buffer[1 + (read_ind % BufSize)];
        if last_read /= read_ind then
            did_proper_read := 0
        end if;
        read_ind := read_ind + 1;
    end if;
  end while;
  
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES buffer, write_ind, read_ind, last_read, did_proper_read, pc

vars == << buffer, write_ind, read_ind, last_read, did_proper_read, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ buffer = [i \in 1..BufSize |-> -1]
        /\ write_ind = BufSize
        /\ read_ind = BufSize
        /\ last_read = 0
        /\ did_proper_read = 1
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "Write"
                                        [] self = 1 -> "Read"]

Write == /\ pc[0] = "Write"
         /\ IF write_ind <= Writes
               THEN /\ IF read_ind + BufSize > write_ind
                          THEN /\ buffer' = [buffer EXCEPT ![1 + (write_ind % BufSize)] = write_ind]
                               /\ write_ind' = write_ind + 1
                          ELSE /\ TRUE
                               /\ UNCHANGED << buffer, write_ind >>
                    /\ pc' = [pc EXCEPT ![0] = "Write"]
               ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                    /\ UNCHANGED << buffer, write_ind >>
         /\ UNCHANGED << read_ind, last_read, did_proper_read >>

writer == Write

Read == /\ pc[1] = "Read"
        /\ IF read_ind <= Writes
              THEN /\ IF read_ind < write_ind
                         THEN /\ last_read' = buffer[1 + (read_ind % BufSize)]
                              /\ IF last_read' /= read_ind
                                    THEN /\ did_proper_read' = 0
                                    ELSE /\ TRUE
                                         /\ UNCHANGED did_proper_read
                              /\ read_ind' = read_ind + 1
                         ELSE /\ TRUE
                              /\ UNCHANGED << read_ind, last_read, 
                                              did_proper_read >>
                   /\ pc' = [pc EXCEPT ![1] = "Read"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                   /\ UNCHANGED << read_ind, last_read, did_proper_read >>
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
\* Last modified Sun Nov 17 22:23:47 EST 2019 by samuelschetterer
\* Created Sun Nov 17 20:26:38 EST 2019 by samuelschetterer
