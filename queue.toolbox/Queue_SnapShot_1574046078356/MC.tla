---- MODULE MC ----
EXTENDS queue, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157404607633973000 ==
read_ind <= write_ind
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_157404607633974000 ==
last_read /= -1
----
=============================================================================
\* Modification History
\* Created Sun Nov 17 22:01:16 EST 2019 by samuelschetterer
