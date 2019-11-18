---- MODULE MC ----
EXTENDS queue, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157404620589175000 ==
read_ind <= write_ind
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_157404620589176000 ==
last_read /= -1
----
=============================================================================
\* Modification History
\* Created Sun Nov 17 22:03:25 EST 2019 by samuelschetterer
