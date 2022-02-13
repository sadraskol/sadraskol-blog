---- MODULE Upload ----
EXTENDS TLC

CONSTANT Docs

VARIABLE token
VARIABLE upload_queue
VARIABLE uploaded

FetchToken ==
    /\ token = "None"
    /\ token' = "Fetched"
    /\ uploaded' = upload_queue
    /\ UNCHANGED <<upload_queue>>

UploadDoc(d) ==
    /\ d \notin upload_queue
    /\ d \notin uploaded
    /\ \/ /\ token = "None"
          /\ upload_queue' = upload_queue \cup {d}
          /\ UNCHANGED <<token, uploaded>>
       \/ /\ token = "Fetched"
          /\ uploaded' = uploaded \cup {d}
          /\ UNCHANGED <<token, upload_queue>>

Init ==
    /\ token = "None"
    /\ upload_queue = {}
    /\ uploaded = {}

Next == 
    \/ FetchToken
    \/ \E d \in Docs: UploadDoc(d)
    \/ /\ Docs = uploaded
       /\ UNCHANGED <<token, upload_queue, uploaded>>

====