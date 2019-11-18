---- MODULE MC ----
EXTENDS queue, TLC

\* INIT definition @modelBehaviorNoSpec:0
init_157404730086088000 ==
FALSE/\did_proper_read = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157404730086089000 ==
FALSE/\did_proper_read' = did_proper_read
----
=============================================================================
\* Modification History
\* Created Sun Nov 17 22:21:40 EST 2019 by samuelschetterer
