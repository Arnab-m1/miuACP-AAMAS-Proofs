---- MODULE muACP_Fixed ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Agents,                 \* Set of agents {a1, a2, a3}
    MaxMemory,             \* Memory bound per Definition 1
    MaxBandwidth,          \* Bandwidth bound
    MaxCPU,                \* CPU cycles bound  
    MaxEnergy,             \* Energy bound
    MaxMsgID,              \* Maximum message ID for headers
    MaxPayloadSize,        \* Maximum payload size in bytes
    MaxTLVOptions,         \* Maximum number of TLV options per message
    MaxOptionValue,        \* Maximum value size for TLV options
    OptionTypes            \* Set of valid TLV option types

VARIABLES
    agentStates,           \* Per-agent state Si = (Mi, Ki, Ti, Hi)
    messageQueue,          \* Message queues per agent
    networkChannels,       \* Network channels between agents
    globalResources,       \* Global resource consumption tracking
    msgIdCounter          \* Message ID counter

\* ============================================================================
\* BASIC DEFINITIONS
\* ============================================================================

\* Definition 1: μACP verbs (exactly as in paper)
Verbs == {"PING", "TELL", "ASK", "OBSERVE"}

\* Definition 4: Well-formed message header (64-bit header from paper)
Header == [
    id: 0..MaxMsgID,           
    seq: 0..10,                \* Bounded sequence number  
    qos: 0..7,                 
    flags: 0..15               
]

\* TLV options simplified for TLC
TLVOption == [
    type: OptionTypes,         
    length: 0..MaxOptionValue, 
    value: 0..MaxOptionValue   
]

\* Definition 4: Well-formed μACP message structure
Message == [
    hdr: Header,                              
    verb: Verbs,                             
    options: Seq(TLVOption),                 
    payload: Seq(0..255),                    
    size: 0..1000                            \* Bounded size
]

\* Simplified agent state
AgentState == [
    memory: 0..MaxMemory,                    
    knowledge: SUBSET (0..100),              \* Simplified knowledge base
    timers: [Agents -> 0..100],              
    history: Seq(Message)                    
]

\* Resource consumption tuple
ResourceConsumption == [
    memory: 0..MaxMemory,                             
    bandwidth: 0..MaxBandwidth,                          
    cpu: 0..MaxCPU,                               
    energy: 0..MaxEnergy                             
]

\* ============================================================================
\* HELPER OPERATORS
\* ============================================================================

\* Range operator for sequences
Range(seq) == {seq[i] : i \in DOMAIN seq}

\* Resource consumption function simplified
ResourceCost(agent, verb, options, payload) ==
    LET baseMemory == 8 + Len(payload) + (Len(options) * 4)
        baseCPU == IF verb = "PING" THEN 5
                   ELSE IF verb = "TELL" THEN 10  
                   ELSE IF verb = "ASK" THEN 15
                   ELSE 12
        baseEnergy == 2 + (Len(payload) \div 10)
    IN [memory |-> baseMemory,
        bandwidth |-> baseMemory,  
        cpu |-> baseCPU,
        energy |-> baseEnergy]

\* ============================================================================
\* WELL-FORMEDNESS PREDICATES
\* ============================================================================

\* Definition 4: Well-formed message predicate (simplified)
WellFormedMessage(msg) ==
    /\ msg.hdr \in Header                    
    /\ msg.verb \in Verbs                    
    /\ Len(msg.options) <= MaxTLVOptions         
    /\ Len(msg.payload) <= MaxPayloadSize       
    /\ msg.size = 8 + Len(msg.payload) + (Len(msg.options) * 4)

\* Resource feasibility predicate
ResourceFeasible(agent, verb, options, payload) ==
    LET cost == ResourceCost(agent, verb, options, payload)
    IN  /\ cost.memory <= MaxMemory
        /\ cost.bandwidth <= MaxBandwidth  
        /\ cost.cpu <= MaxCPU
        /\ cost.energy <= MaxEnergy

\* ============================================================================
\* INITIAL STATE
\* ============================================================================

Init ==
    /\ agentStates = [a \in Agents |-> [
         memory |-> 0,
         knowledge |-> {},
         timers |-> [b \in Agents |-> 0],
         history |-> <<>>
       ]]
    /\ messageQueue = [a \in Agents |-> <<>>]
    /\ networkChannels = [pair \in Agents \times Agents |-> <<>>]
    /\ globalResources = [memory |-> 0, bandwidth |-> 0, cpu |-> 0, energy |-> 0]
    /\ msgIdCounter = 0

\* ============================================================================
\* OPERATIONAL SEMANTICS
\* ============================================================================

\* Create a well-formed μACP message
CreateMessage(sender, receiver, verb, options, payload) ==
    LET msgSize == 8 + Len(payload) + (Len(options) * 4)
        seqNum == Len(agentStates[sender].history)
    IN [hdr |-> [id |-> msgIdCounter, seq |-> seqNum, qos |-> 0, flags |-> 0],
        verb |-> verb,
        options |-> options, 
        payload |-> payload,
        size |-> msgSize]

\* Send action with bounds checking
Send(sender, receiver, verb, options, payload) ==
    /\ sender \in Agents 
    /\ receiver \in Agents
    /\ sender # receiver
    /\ msgIdCounter < MaxMsgID
    /\ Len(messageQueue[receiver]) < 5  \* Queue bound
    /\ Len(agentStates[sender].history) < 10  \* History bound
    /\ LET msg == CreateMessage(sender, receiver, verb, options, payload)
       IN  /\ WellFormedMessage(msg)
           /\ ResourceFeasible(sender, verb, options, payload)  
           /\ LET cost == ResourceCost(sender, verb, options, payload)
              IN  /\ globalResources.memory + cost.memory <= MaxMemory
                  /\ globalResources.bandwidth + cost.bandwidth <= MaxBandwidth
                  /\ globalResources.cpu + cost.cpu <= MaxCPU  
                  /\ globalResources.energy + cost.energy <= MaxEnergy
                  /\ messageQueue' = [messageQueue EXCEPT ![receiver] = Append(@, msg)]
                  /\ agentStates' = [agentStates EXCEPT 
                       ![sender].history = Append(@, msg)]
                  /\ globalResources' = [globalResources EXCEPT 
                       !.memory = @ + cost.memory,
                       !.bandwidth = @ + cost.bandwidth,
                       !.cpu = @ + cost.cpu,
                       !.energy = @ + cost.energy]
                  /\ msgIdCounter' = msgIdCounter + 1
                  /\ UNCHANGED networkChannels

\* Process message 
ProcessMessage(receiver) ==
    /\ receiver \in Agents
    /\ Len(messageQueue[receiver]) > 0
    /\ LET msg == Head(messageQueue[receiver])
       IN  /\ messageQueue' = [messageQueue EXCEPT ![receiver] = Tail(@)]
           /\ agentStates' = [agentStates EXCEPT ![receiver] = 
                [@ EXCEPT !.knowledge = @ \cup {msg.hdr.id},
                          !.history = IF Len(@) < 10 THEN Append(@, msg) ELSE @]]
           /\ LET cost == ResourceCost(receiver, msg.verb, msg.options, msg.payload)
              IN  globalResources' = [globalResources EXCEPT
                    !.memory = IF @ >= cost.memory THEN @ - cost.memory ELSE 0,
                    !.cpu = @ + (cost.cpu \div 2)]
           /\ UNCHANGED <<networkChannels, msgIdCounter>>

\* ============================================================================
\* NEXT STATE TRANSITIONS
\* ============================================================================

Next ==
    \/ \E sender, receiver \in Agents :
         /\ sender # receiver  
         /\ Send(sender, receiver, "PING", <<>>, <<1, 2>>)
    \/ \E sender, receiver \in Agents :
         /\ sender # receiver
         /\ Send(sender, receiver, "TELL", <<>>, <<3, 4, 5>>)
    \/ \E receiver \in Agents : 
         ProcessMessage(receiver)

\* ============================================================================
\* SPECIFICATION
\* ============================================================================

Spec == Init /\ [][Next]_<<agentStates, messageQueue, networkChannels, globalResources, msgIdCounter>>

\* ============================================================================
\* INVARIANTS AND PROPERTIES
\* ============================================================================

\* Type correctness
TypeOK ==
    /\ agentStates \in [Agents -> AgentState]
    /\ messageQueue \in [Agents -> Seq(Message)]
    /\ globalResources \in ResourceConsumption
    /\ msgIdCounter \in 0..MaxMsgID

\* Resource boundedness 
ResourceBoundedness ==
    /\ globalResources.memory <= MaxMemory
    /\ globalResources.bandwidth <= MaxBandwidth
    /\ globalResources.cpu <= MaxCPU
    /\ globalResources.energy <= MaxEnergy

\* Well-formedness of all messages
MessageWellFormedness ==
    /\ \A agent \in Agents :
         \A i \in DOMAIN messageQueue[agent] : 
           WellFormedMessage(messageQueue[agent][i])
    /\ \A agent \in Agents :
         \A i \in DOMAIN agentStates[agent].history :
           WellFormedMessage(agentStates[agent].history[i])

\* Semantic consistency
SemanticConsistency ==
    \A agent \in Agents :
      \A i \in DOMAIN agentStates[agent].history :
        LET msg == agentStates[agent].history[i]
        IN CASE msg.verb = "PING" -> TRUE  
           []   msg.verb = "TELL" -> Len(msg.payload) > 0  
           []   msg.verb = "ASK" -> Len(msg.payload) > 0   
           []   msg.verb = "OBSERVE" -> TRUE  

\* Queue bounds
QueueBounds ==
    \A agent \in Agents : Len(messageQueue[agent]) <= 5

\* History bounds  
HistoryBounds ==
    \A agent \in Agents : Len(agentStates[agent].history) <= 10

====

---- MODULE muACP_Fixed ----
EXTENDS Integers, Sequences, FiniteSets, TLC

\* ... [previous content remains the same] ...

\* ============================================================================
\* ADDITIONAL INVARIANTS FOR BOUNDS CHECKING
\* ============================================================================

\* Message ID bounds
MsgIdBounds == msgIdCounter <= MaxMsgID

\* Queue bounds (replaces config constraint)
QueueBounds == 
    \A agent \in Agents : Len(messageQueue[agent]) <= 5

\* History bounds (replaces config constraint)  
HistoryBounds ==
    \A agent \in Agents : Len(agentStates[agent].history) <= 10

\* Global resource bounds (replaces config constraint)
GlobalResourceBounds ==
    /\ globalResources.memory <= MaxMemory
    /\ globalResources.bandwidth <= MaxBandwidth
    /\ globalResources.cpu <= MaxCPU
    /\ globalResources.energy <= MaxEnergy

\* ============================================================================
\* EXISTING INVARIANTS (keep these)
\* ============================================================================

TypeOK ==
    /\ agentStates \in [Agents -> AgentState]
    /\ messageQueue \in [Agents -> Seq(Message)]
    /\ globalResources \in ResourceConsumption
    /\ msgIdCounter \in 0..MaxMsgID

ResourceBoundedness ==
    /\ globalResources.memory <= MaxMemory
    /\ globalResources.bandwidth <= MaxBandwidth
    /\ globalResources.cpu <= MaxCPU
    /\ globalResources.energy <= MaxEnergy

MessageWellFormedness ==
    /\ \A agent \in Agents :
         \A i \in DOMAIN messageQueue[agent] : 
           WellFormedMessage(messageQueue[agent][i])
    /\ \A agent \in Agents :
         \A i \in DOMAIN agentStates[agent].history :
           WellFormedMessage(agentStates[agent].history[i])

SemanticConsistency ==
    \A agent \in Agents :
      \A i \in DOMAIN agentStates[agent].history :
        LET msg == agentStates[agent].history[i]
        IN CASE msg.verb = "PING" -> TRUE  
           []   msg.verb = "TELL" -> Len(msg.payload) > 0  
           []   msg.verb = "ASK" -> Len(msg.payload) > 0   
           []   msg.verb = "OBSERVE" -> TRUE  



====




