---- MODULE MC ----
EXTENDS queue, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157404743151196000 ==
read_ind <= write_ind
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_157404743151197000 ==
last_read /= -1
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_157404743151198000 ==
did_proper_read = 1
----
=============================================================================
\* Modification History
\* Created Sun Nov 17 22:23:51 EST 2019 by samuelschetterer
