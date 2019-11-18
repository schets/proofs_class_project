---- MODULE MC ----
EXTENDS queue, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157404597181469000 ==
read_ind <= write_ind
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_157404597181470000 ==
last_read /= -1
----
=============================================================================
\* Modification History
\* Created Sun Nov 17 21:59:31 EST 2019 by samuelschetterer
