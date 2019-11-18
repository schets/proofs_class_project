---- MODULE MC ----
EXTENDS queue, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157404582734663000 ==
read_ind <= write_ind
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_157404582734664000 ==
last_read /= -1
----
=============================================================================
\* Modification History
\* Created Sun Nov 17 21:57:07 EST 2019 by samuelschetterer
