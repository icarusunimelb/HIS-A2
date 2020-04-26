/* Simplified model of PGP key server
 *
 * SWEN90010 2020 - Assignment 2
 *
 * Submission: <Yinsong-Chen-945600> <Ning-Jin-889797>
 */

open util/ordering[State] as ord

// STATE OF THE SYSTEM //////////////////////////////////////////////////

abstract sig Data {}

// Keys, stored by the key server
sig Key extends Data {}

// Tokens, issued for identity confirmation
sig Token extends Data {}

// represents email addresses like bob@example.com
sig Identity {}

// The User and the Attacker each have their own email encryption key and id
one sig UserKey, AttackerKey extends Key {}
one sig UserId, AttackerId extends Identity {}

// represents the different types of messages
abstract sig MessageSubject {}
one sig RegisterRequest, RegisterResponse, 
        ConfirmRequest extends MessageSubject {}

// Messages, which contain their subject and optional data
// the addr is either the message's sender or the receiver: for Request 
// messages, addr is the sender; for Response messages, addr is the 
// intended receiver.
// the key_check will be used to prevent the attacker tampering the RegisterRequest message
sig Message {
  addr : Identity,
  subject : MessageSubject,
  contents : set Data,
  key_check : Key // TASK3
}

// A special value to indicate that an identity has been confirmed.
// CONFIRMED is not a real token
one sig CONFIRMED extends Token {}

// valid tokens are not the CONFIRMED token
pred valid_token[t : Token] {
  t not in CONFIRMED
}

// some debugging information to make it easier to interpret the traces 
// returned by Alloy when looking for counter-examples, etc. Specifically,
// we remember in the state whether it was the Server, Attacker or the 
// User who performed the most recent action
abstract sig DEBUG_Who {}
one sig DEBUG_Server, DEBUG_Attacker, DEBUG_User, DEBUG_None extends DEBUG_Who {}

// the state includes the key server state (keys) plus the network. 
// we also track the tokens known to the attacker.
// To make it easier to interpret counter-examples returned by Alloy, 
// we include the DEBUG_Last_Action_Who field which records in the state 
// who performed the last action
sig State {
  keys: Key -> Identity -> lone Token,
  network : lone Message,
  attacker_knowledge : set Token,
  DEBUG_Last_Action_Who : DEBUG_Who
}

// whether a key and identity association has been confirmed
pred is_confirmed[s : State, k : Key, id: Identity]  {
  s.keys[k][id] = CONFIRMED
}


// MESSAGE PREDICATES ////////////////////////////////////////////////////
//
// The following predicates define for each message subject (i.e. for each
// type of message) whether a message m is a valid message of that type.
//
// NOTE: When carrying out Task 3 you may need to modify one or
//       more of these predicates. If do modify them, make sure you
//       explain how you modified them in the comments

// whether message is a valid RegisterRequest message for k and id
pred is_register_request[m : Message, k : Key, id : Identity] {
  m.addr = id and m.subject = RegisterRequest and k = m.contents
}

// whether message is a valid RegisterResponse message for id and t
pred is_register_response[m : Message, id: Identity, t : Token] {
  m.addr = id and m.subject = RegisterResponse and t = m.contents
}

// whether message is a valid ConfirmRequest message for id and t
pred is_confirm_request[m : Message, id : Identity, t : Token] {
  m.addr = id and m.subject = ConfirmRequest and t = m.contents
}


// ACTION PREDICATES //////////////////////////////////////////////////////

// Note: these predicates don't talk about DEBUG_Action_Last_Who, which is
// handled separately below. This is intentional.

// Represents the action of sending a RegisterRequest message to register
// the association between key k and identity id
//
// Precondition:  - None
//
// Postcondition: - network now contains a valid RegisterRequest message for 
//                             k and id; 
//                          - keys and attacker_knowledge unchanged 
pred send_register_request[s,s': State, k : Key, id: Identity] {
  some m : Message | is_register_request[m,k,id] and s'.network = s.network + m 
  s'.keys = s.keys
  s'.attacker_knowledge = s.attacker_knowledge
}

// Represents the server receiving a RegisterRequest message for k and id,
// and then generating the token t. 
//
// YOUR TASK: Describe in comments the pre and post-conditions (3 marks)
//
// Precondition:  - k hasn't been registered in the server;
//		      - t is a vaild token, which means t is not CONFIRMED;
//		      - network contained a valid RegisterRequest message for k and id;
//		      - the server doesn't have any (Key, Identity, Token) triples contain t;
//
// Postcondition: - network now contains a valid RegisterResponse message for id and t;
// 		       - the RegisterRequest message has been removed from the network
//		       - the triple (k, id, t) is added to keys
// 		       - attacker knowledge is unchanged
//		       - (Task 3) the RegisterResponse message's key_check attribute is k
pred recv_register_request[s, s' : State, k : Key, id: Identity, t : Token] {
  no k <: s.keys
  valid_token[t]
  some mreq, mresp : Message | ( 
    is_register_request[mreq,k,id] and 
    is_register_response[mresp,id,t] and
    mreq in s.network and s'.network = (s.network - mreq) + mresp
    and s'.network.key_check = k // TASK3
  )
  t not in s.keys[Key][Identity]
  s'.keys = s.keys + (k -> id -> t) 
  s'.attacker_knowledge = s.attacker_knowledge
}

// Represents the action of sending a ConfirmRequest message for id and t
//
// YOUR TASK: Describe in comments the pre and post-conditions (1 mark)
//
// Precondition:  - network contained no Message
//
// Postcondition: - network now contains a valid ConfirmRequest message for
//                  	      id and t;
//		            - keys and attacker_knowledge unchanged 
pred send_confirm_request[s,s' : State, id : Identity, t : Token] {
  some mreq : Message | is_confirm_request[mreq, id, t] and 
    s'.network = s.network + mreq
   s'.keys = s.keys
   s'.attacker_knowledge = s.attacker_knowledge
}

// Represents the server receiving a ConfirmRequest message to confirm
// the association between key k, identity id, using token t
//
// Precondition:  - network contains a valid ConfirmRequest msg for id and t
//                          - the server has a triple (k,id,t) stored
// Postcondition: - the ConfirmRequest message is removed from the network
//                           - the triple (k,id,t) is updated to (k,id,CONFIRMED)
//                           - attacker knowledge is unchanged
pred recv_confirm_request[s, s' : State, k : Key, id : Identity, t : Token] {
  some mreq : Message | (is_confirm_request[mreq, id, t] and 
                         mreq in s.network and 
                         s'.network = s.network - mreq)
  t in s.keys[k][id]
  s'.keys = s.keys ++ (k->id->CONFIRMED)
  s'.attacker_knowledge = s.attacker_knowledge
}

// Represents looking-up which key is associated with an id in the server
// This predicate holds (i.e. is true) only when the association between
// the key and the id have been confirmed.
pred lookup_key[s : State, k : Key, id : Identity] {
  is_confirmed[s,k,id]
}


// ACTIONS OF THE USER, SERVER AND THE ATTACKER

// This predicate represents the action of the user receiving and responding
// to a RegisterResponse message sent from the PGP Key Server.
// 
// YOUR TASK: Implement this predicate (3 marks)
//
// NOTE: When carrying out Task 3 you may need to modify the predicate
//       Make sure you update the comments if you do that to describe how
//       it was modified.
//
// Precondition:  - There is a valid RegisterReponse message on the network
//                  for UserId containing some token t
// 		      - (Task 3) The key_check attribute in the RegisterReponse message 
//		is equal to UserKey
//                
// Postcondition: - There is a valid ConfirmRequest message on the network
//                  for the user's id UserId and token t
//                - The RegisterResponse message has been removed from
//                  the network
//                - Attacker knowledge and server keys unchanged 
pred user_recv_register_response[s,s' : State] {
  some mresp, mreq : Message, t : Token | (
	is_register_response[mresp, UserId, t] and 
	is_confirm_request[mreq, UserId, t] and 
	mresp.key_check in UserKey and // TASK3
	mresp in s.network and s'.network = (s.network - mresp) + mreq
	)
  s'.keys = s.keys
  s'.attacker_knowledge = s.attacker_knowledge
}

// This predicate represents the actions of the server. These are
// receiving RegisterRequest messages and ConfirmRequest messages
pred server_action[s,s' : State] {
 some t : Token, id : Identity, key : Key | 
   recv_register_request[s,s',key,id,t] or
   recv_confirm_request[s,s',key,id,t]
}

// This predicate represents the actions of the User. These are
// 1. sending RegisterRequest messages to register the user's key UserKey 
//    with the user's id UserId, and
// 2. Receiving and responding to a RegisterResponse message
pred user_action[s,s' : State] {
  send_register_request[s,s',UserKey,UserId] or
  user_recv_register_response[s,s']
}


// Attacker actions. DO NOT MODIFY THIS PREDICATE 
// Part of your job is to understand what this predicate is saying
// in terms of what it allows the attacker to do on the network and what
// it says the attacker can NOT do
pred attacker_action[s,s' : State] {
  s'.keys = s.keys
  s'.attacker_knowledge = s.attacker_knowledge + (s.network.contents & Token)
  (no s'.network or 
  (some m, m' : Message | m in s.network and m' in s'.network and 
                          m'.contents in s'.attacker_knowledge + AttackerKey and 
                          m'.addr in m.addr and m'.subject in m.subject)) or
  (some m' : Message | no s.network and m' in s'.network and
                          m'.contents in s'.attacker_knowledge + AttackerKey and
                          m'.addr = AttackerId)
}



// PROPERTIES OF THE SYSTEM ////////////////////////////////////////////

// ids that are looked-up must be confirmed
assert lookup_key_is_confirmed {
  all s : State, k : Key, id : Identity |
    lookup_key[s,k,id] => is_confirmed[s,k,id]
}

check lookup_key_is_confirmed for 3 expect 0

// ATTACKER ABILITIES (Task 2) /////////////////////////////////////////

// YOUR TASK: Fill in each of the following predicates which describe
//            different abilities that the attacker may or may not have
//            Then, by using Alloy's "run" command and by examining the
//            definition of attacker_action above, work out whether the
//            attacker does or does not have that ability. If the attacker
//            has that ability, the "run" command should generate an
//            example. 
//            For each ability and "run" command, add an "expect" 
//            annotation: "expect 1" if the attacker has that ability;
//                       " expect 0" if the attacker does not have it
//
// (5 marks)
//
// An example attacker ability: that the attacker can learn tokens found 
// in messages on the network. Specifically that attacker_action can occur
// from state s to state s' and that the attacker knowledge contains
// something new in s' that wasn't in s
pred attacker_can_learn_tokens[s,s' : State] {
  attacker_action[s,s'] and 
  some k : Token | k in s'.attacker_knowledge and 
                   k not in s.attacker_knowledge
}

// clearly the attacker has this ability (although we need a relatively
// large bound to find it). So we annotate this is "expect 1"
run attacker_can_learn_tokens for 7 expect 1

// YOUR TASK: Implement the remainder of this predicate.
// It describes the potential ability of the attacker to remove messages
// from the network
pred attacker_can_drop[s,s' : State] {
  attacker_action[s,s'] and
  some m:Message | m in s.network and no s'.network
}

// NOTE: you will probably need to tweak the bound 
// YOUR TASK: annotate this with "expect 0/1"
//            1 if the attacker has this ability
//            0 if the attacker does not have this ability
run attacker_can_drop for 3 expect 1


// YOUR TASK: Implement the remainder of this predicate.
// It describes the potential ability of the attacker to modify
// messages on the network
pred attacker_can_modify_messages[s,s' : State] {
  attacker_action[s,s'] and
  some m, m':Message | ( m in s.network and
	m' in s'.network and 
	( m.addr != m'.addr or 
	  m.subject != m'.subject or 
	  m.contents!=m'.contents))
}

// NOTE: you will probably need to tweak the bound 
// YOUR TASK: annotate this with "expect 0/1"
//            1 if the attacker has this ability
//            0 if the attacker does not have this ability
run attacker_can_modify_messages for 3 expect 1

// YOUR TASK: Implement the remainder of this predicate.
// It describes the potential ability of the attacker to put a
// message onto the network whose addr is UserId when there was no
// UserId message already on the network
pred attacker_can_forge_id[s,s' : State] {
  attacker_action[s,s'] and 
  ((some m, m':Message | m in s.network and 
	m' in s'.network and 
	m'.contents in m.contents and 
	m'.subject in m.subject and 
	m.addr = AttackerId and 
	m'.addr = UserId)or(
	some m':Message | no s.network and 
	m' in s'.network and 
	m'.addr = UserId))
}

// NOTE: you will probably need to tweak the bound 
// YOUR TASK: annotate this with "expect 0/1"
//            1 if the attacker has this ability
//            0 if the attacker does not have this ability
run attacker_can_forge_id for 3 expect 0


// YOUR TASK: Implement the remainder of this predicate.
// It describes the potential ability of the attacker to put a new
// message onto the network when there was no message before
pred attacker_can_inject[s,s' : State] {
  attacker_action[s,s'] and
  some m:Message | no s.network and m in s'.network
}

// NOTE: you will probably need to tweak the bound 
// YOUR TASK: annotate this with "expect 0/1"
//            1 if the attacker has this ability
//            0 if the attacker does not have this ability
run attacker_can_inject for 3 expect 1


// STATE PREDICATES /////////////////////////////////////////////////////

// This predicate describes the initial state of the system:
// - The server stores no information
// - The network is empty
// - The attacker knows no tokens
// - There is no DEBUG_Last_Action_Who since there is no prior action
pred init[s : State] {
  no s.keys
  no s.network
  no s.attacker_knowledge
  s.DEBUG_Last_Action_Who = DEBUG_None
}

// This predicate describes "good" or "secure" states of the system.
// A state is secure if when we look up the key associated with the
// user's id UserId, the only key we find (if any) is the user's key UserKey
// (and e.g. not the attacker's key)
pred good_state[s : State]{
  all k : Key | lookup_key[s,k,UserId] => k in UserKey
}

// TRACES OF STATES ////////////////////////////////////////////////////

// A state transition occurs either when the user, attacker or server
// does an action
pred state_transition[s,s' : State] {
  user_action[s,s'] and s'.DEBUG_Last_Action_Who = DEBUG_User or
  attacker_action[s,s'] and s'.DEBUG_Last_Action_Who = DEBUG_Attacker or
  server_action[s,s'] and s'.DEBUG_Last_Action_Who = DEBUG_Server
}

// We use ord on states to represent sequences (traces) of transitions
fact state_transition {
  all s: State, s': ord/next[s] {
    state_transition[s,s'] 
  }
}

// The first state in a trace is the initial state
fact init_state {
  init[ord/first]
}


// PROPERTIES THAT THE SYSTEM SHOULD SATISFY /////////////////////////////


// A sanity check that the initial state is good (secure)
assert init_state_is_good {
  good_state[ord/first]
}

check init_state_is_good for 5 expect 0

// A sanity check that the user is able to register their own key and id
pred user_can_register_key[s : State] {
  lookup_key[s,UserKey,UserId]
}

run user_can_register_key for 4 but 5 State, 2 Identity, 2 Key expect 1


// The main property we want the system to satisfy: all states are secure
assert no_bad_states {
  all s : State | good_state[s]
}

// At the end of Task 1 you should find that this predicate does NOT hold
//
// YOUR TASK (3 marks): Describe the counter-example (attack) here in comments
//
// After the user sent the Register Request message to the network,
// the attacker will intercept the Register Request message, 
// modify the content from the UserKey to AttackerKey,
// then send the modified Register Request message to the server. 
//
// In Task 3 you will modify the protocol to make the predicate hold
check no_bad_states for 5 but 2 Key, 2 Identity, 3 Token, 6 State

// HOW WE FIXED THE VULNERABILITY
//
// - To fix the vulunerability, we add a key_check attribute in the message class.
// - We also modified the recv_register_request predicate to make the server will add the key it accepted 
//   to the key_check attribute of the Register Response message.
// - Another modification we have done is that we modify the user_recv_register_response predicate to add a 
//   precondition that the key_check attribute of the Register Response message should be UserId. 
// - Hence, totally we have done three modifications and each modification has been added an "Task 3" 
//   comment as postfix.
// - As a result, now after the attacker modified the key of Register Request message, the server will add
//   the modified key which is AttackerKey to the key_check part of the Register Response message. When 
//   the user received the Register Response message, he would check if the key_check attribute in the 
//   Register Response message is equal to the UserKey he sent. If the key_check attribute isn't equal to
//   the UserKey, it means the Register Request message has been modified by the attacker. Therefore, the 
//   user will reject to confirm the registration request. 
