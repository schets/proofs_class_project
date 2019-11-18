---- MODULE MC ----
EXTENDS queue, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157404587927867000 ==
read_ind <= write_ind
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_157404587927868000 ==
last_read /= -1
----
=============================================================================
\* Modification History
\* Created Sun Nov 17 21:57:59 EST 2019 by samuelschetterer
