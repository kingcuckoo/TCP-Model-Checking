------------------------------- MODULE TCPReno -------------------------------

EXTENDS Naturals

CONSTANTS InitialCwnd, LargeValue

VARIABLES cwnd, ssthresh, dupACKcount, mode

(* Possible modes *)
Modes == {"SlowStart", "CongestionAvoidance", "FastRetransmit"}

(* Initialization *)
Init ==
    /\ cwnd = InitialCwnd
    /\ ssthresh = LargeValue
    /\ dupACKcount = 0
    /\ mode = "SlowStart"

(* Transition on ACK receipt *)
AckReceipt == 
    /\ IF mode = "SlowStart" THEN
          /\ cwnd' = cwnd + 1
          /\ IF cwnd' >= ssthresh THEN
                mode' = "CongestionAvoidance"
             ELSE
                mode' = mode
       ELSE IF mode = "CongestionAvoidance" THEN
          /\ cwnd' = cwnd + 1 \div cwnd (* This is a simplification *)
          /\ mode' = mode
       ELSE
          /\ cwnd' = cwnd
          /\ dupACKcount' = 0
          /\ mode' = "CongestionAvoidance"

(* Transition on Duplicate ACK receipt *)
DupAckReceipt ==
    /\ dupACKcount' = dupACKcount + 1
    /\ IF dupACKcount' >= 3 /\ mode /= "FastRetransmit" THEN
          /\ ssthresh' = cwnd \div 2
          /\ cwnd' = ssthresh' + 3
          /\ mode' = "FastRetransmit"
       ELSE
          /\ ssthresh' = ssthresh
          /\ cwnd' = cwnd
          /\ mode' = mode

(* Transition on Timeout *)
Timeout ==
    /\ ssthresh' = cwnd \div 2
    /\ cwnd' = InitialCwnd
    /\ dupACKcount' = 0
    /\ mode' = "SlowStart"

(* Next state relation *)
Next ==
    \/ AckReceipt
    \/ DupAckReceipt
    \/ Timeout

=============================================================================
