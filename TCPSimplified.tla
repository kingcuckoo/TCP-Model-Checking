------------------------------ MODULE TCPSimplified ------------------------------

EXTENDS Naturals, Sequences

(* State Definitions *)
VARIABLES connectionState, dataToSend, unacknowledgedData, receivedData, data

(* Connection states *)
States == {"CLOSED", "LISTEN", "SYN_SENT", "SYN_RECEIVED", "ESTABLISHED", "FIN_WAIT_1", "FIN_WAIT_2", "CLOSE_WAIT", "LAST_ACK", "TIME_WAIT", "CLOSING"}

Init ==
    /\ connectionState = "CLOSED"
    /\ dataToSend = <<>> (* Empty sequence for data *)
    /\ unacknowledgedData = <<>> (* Empty sequence for unacknowledged data *)
    /\ receivedData = <<>> (* Empty sequence for received data *)
    /\ data = <<>>

(* Start a connection with a 3-way handshake *)
StartConnection ==
    /\ connectionState = "CLOSED"
    /\ connectionState' = "SYN_SENT"
    
ReceiveSYN ==
    /\ connectionState = "LISTEN"
    /\ connectionState' = "SYN_RECEIVED"
    
AcknowledgeSYN ==
    /\ connectionState = "SYN_RECEIVED"
    /\ connectionState' = "ESTABLISHED"

(* Send and receive data *)
SendData ==
    /\ connectionState = "ESTABLISHED"
    /\ dataToSend' = Append(dataToSend, data)
    /\ unacknowledgedData' = Append(unacknowledgedData, data)
    
ReceiveData ==
    /\ connectionState = "ESTABLISHED"
    /\ receivedData' = Append(receivedData, data)

AcknowledgeData ==
    /\ connectionState = "ESTABLISHED"
    /\ unacknowledgedData' = Tail(unacknowledgedData) (* Remove first element, considering it's acknowledged *)

(* Terminate a connection with a 4-way handshake *)
InitiateTermination ==
    /\ connectionState = "ESTABLISHED"
    /\ connectionState' = "FIN_WAIT_1"

ReceiveFIN ==
    /\ connectionState \in {"ESTABLISHED", "FIN_WAIT_1"}
    /\ connectionState' = IF connectionState = "ESTABLISHED" THEN "CLOSE_WAIT" ELSE "CLOSING"

AcknowledgeFIN ==
    /\ connectionState \in {"FIN_WAIT_1", "CLOSING", "LAST_ACK"}
    /\ connectionState' = "FIN_WAIT_2"
    
EndConnection ==
    /\ connectionState \in {"FIN_WAIT_2", "TIME_WAIT"}
    /\ connectionState' = "CLOSED"

Next ==
    \/ StartConnection
    \/ ReceiveSYN
    \/ AcknowledgeSYN
    \/ SendData
    \/ ReceiveData
    \/ AcknowledgeData
    \/ InitiateTermination
    \/ ReceiveFIN
    \/ AcknowledgeFIN
    \/ EndConnection

=============================================================================
