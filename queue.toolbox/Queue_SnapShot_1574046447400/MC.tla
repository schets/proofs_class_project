---- MODULE MC ----
EXTENDS queue, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157404644452577000 ==
read_ind <= write_ind
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_157404644452578000 ==
last_read /= -1
----
=============================================================================
\* Modification History
\* Created Sun Nov 17 22:07:24 EST 2019 by samuelschetterer
