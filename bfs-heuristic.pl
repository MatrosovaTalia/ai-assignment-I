/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Implementation of  Introduction to AI Assignment I
   This solution is based on Alexander Cska Roque solution of
   Wumpus World game.


   Glossary:
    TD - Touchdown position
    ballPlayer - the actor from humans team, who is currently holding the ball
    R = r(X,Y) - field at position X,Y (used as position)
    S - used as situations
    do(A,S) - the situation after doing action A on situation S.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

% These must be dynamic so that many different worlds might be created
% at runtime.


:- dynamic([
    w_Wall/1,
    w_Human/1,
    w_Touchdown/1,
    w_Orc/1
  ]).
  
  %CONSTANTS
  maxNumberOfExploredFields(100).
  maxNumberOfActionsPlanned(20).
  
  %INITIAL CONDITIONS AND STATE-SUCCESSOR AXIOMS
  ballPlayer(r(1,1),e,s0). 
  ballPlayer(R,D,do(A,S)) :- ballPlayer(R0,D0,S), %get ballPlayer info at last situation
      ( %if action changes ballPlayer position
          (A = left, R = R0, ((D0 = n, D = w);(D0 = e, D = n);(D0 = s, D = e);(D0 = w, D = s))); %turn left
          (A = right, R = R0, ((D0 = n, D = e);(D0 = e, D = s);(D0 = s, D = w);(D0 = w, D = n))); %turn right
          (A = forward, D = D0, getForwardField(R0,D0,RN), !, (w_Wall(RN) -> R = R0 ; R = RN)) %go forward
      );
      ( %no actions that change ballPlayer position happened
          ballPlayer(R,D,S), %Position of ballPlayer now same as before
          \+A = left,
          \+A = right,
          \+A = forward
      ).
  
  
  % GAME STATE
  % Indicates whether the ball was lost after a throw or not
  ballInGame(s0). %Starts with ball
  ballInGame(do(A,S)) :- ballInGame(S), 
      ((A = throwBall, canThrowBall(S), ballPlayer(R0,D0,S), w_Human(RW), isFacing(R0,D0,RW)) -> false ; true).
  
  % Indicates whether human team has performed a throw or not
  canThrowBall(s0). % initially can
  canThrowBall(do(A,S)) :- %Return false and stays false after using throwBall action once
      (   A = throwBall -> false ; canThrowBall(S)).
  
  %Indicates whether ballPlayer has reached the touchdown
  reachedTouchdown(s0) :- false. % Initially starts not on touchdown 
  reachedTouchdown(do(A,S)) :-
      (reachedTouchdown(S); (A = putBall, w_Touchdown(R), ballPlayer(R,_,S)) ).
  % To reach the touchdown actor must perform special action (putBall)on TD field
  
  %PERCEPTIONS
  seeTouchdown(S,RT) :- ballPlayer(R,_,S), w_Touchdown(RT), isAdjacent(R,RT).
  onTouchdown(S) :- ballPlayer(R,_,S), w_Touchdown(R). 
  onFieldWithHuman(S) :- ballPlayer(R,_,S), w_Human(R).
  
  %WORLD KNOWLEDGE
  visited(r(1,1),s0).
  visited(R,do(A,S)) :- ballPlayer(R,_,do(A,S)) ; visited(R,S). 
  %Actor remembers all fields that were visited
  touchdown(R,do(A,S)) :- (onTouchdown(do(A,S)),ballPlayer(R,_,do(A,S))) ; touchdown(R,S). 
  % After reaching the TD actor knows where TD is
  
  
  %WORLD EVALUATION
  isOkField(R,_) :- \+w_Orc(R), \+w_Wall(R).
  % field is ok: if it is nor wall nor orc
  
  % HEURISTIC
  heuristic(S,H) :-
      getAllExplorableFields(S,L), %Get entire list of all fields adjacent to fields that were visited
      (\+L=[] -> getBetterExplorableField(S,L,P,R) ; P = 5000), 
      %Only run ranking of Fields if there are not visited fields
      (   reachedTouchdown(S) -> H = putBall 
                %If ballPlayer is on TD, putBall
      ;   (\+reachedTouchdown(S), touchdown(_R,S)) -> H = winTheGame 
                %If not on TD, but knows where it is, go to it
      ;   onFieldWithHuman(S) -> H = pass(R) 
                % if on the same field with human, pass ball and get free move
      ;   P < 100 -> H = move(R) 
                % Move only if the best field is legal to move (no orcs/walls)
      ;   H = giveUp %If no Fields to explore, and TD is not reached give up
      ).
  
  % Finds the field with the smallest rank (least dangerous and closest).
  getBetterExplorableField(S,L,P,R) :-
      rankFields(L,S,RL),
      sort(RL,SRL),
      [Head|_] = SRL,
      rr(P,R) = Head.
  
  % Ranks Fields by number of actions to explore and danger levels
  rankFields([],_,[]).
  rankFields([H|T],S,RL) :-
      rankFields(T,S,LT),
      %Count actions
      doMove(H,ST,S),
      % If Actor sees touchdown it should go to it
      (seeTouchdown(S,H) -> NActions = 0 ; countActions(ST,S,NActions)),  
  
      (isOkField(H,_) -> DangerPoints = 0; DangerPoints = 100),
      Total is NActions + DangerPoints,
      RR = rr(Total,H),
      add(RR,LT,RL).
  
  %PLANNING
  % The following functions are used to plan the movements. Planning performs 
  % a breadth first search from a certaint situtation (S) using available actions 
  % from action list (doActions) to reach the desired field.  
  % 1. Form the list of all explorable (those that are adjacent to the visited
  %  fields, but not visited yet) fields.
  % 2. Assign a rank (number of moves to reach the field + danger level of field)
  % for each field in the list.
  % 3. Sort the fields in the list (the smaller the better).
  % 4. Choose according to the field with the smallest rank will 
  % be chosen as next field to explore from explorable list.
  % 5. After the goal field is chosen Planning according to the heuristic(S,H) 
  % will perform BFS to determine the best sequence of actions H from situation S 
  % to reach goal. 
  
  poss(forward,S) :- %Allow planning only on visited and ok Fields.
      ballPlayer(R,D,S),
      getForwardField(R,D,RF),
      isOkField(RF,_).
  poss(left,s0).
  poss(left,do(A,_S)) :- \+A = right. %Limit redundant turning
  poss(right,s0).
  poss(right,do(A,_S)) :- \+A = left. %Limit redundant turning
  
  legal(S,S). %If S is legal, S is legal
  legal(do(A,S),S0):-
      maxNumberOfActionsPlanned(Max), %Get maximum allowed number of actions
      legal(S,S0), %Tries to find legal actions, starting from provided situation S0
      countActions(S,S0,N), %Count number of actions from S0 to S
      (N > Max -> (!, write('The path is too long, I am get lost'),false) ; true),
       %If too many actions are being taken, probably there is no solution, hence return false
      poss(A,S). %Check which actions are allowed at S
  
  doMove(Rm, S0, S0) :- ballPlayer(Rm,_,S0). %Moving to where the ballPlayer is returns no actions
  doMove(Rm, do(forward,S), S0) :- legal(S,S0),ballPlayer(R,D,S),isAdjacent(R,Rm),isFacing(R,D,Rm),!.
  doFace(Rm, S, S0) :- legal(S,S0),ballPlayer(R,D,S),isFacing(R,D,Rm),!. %Similar to doMove, but only faces de target
  
  %ACTUATOR
  doActions(H,S,S0) :-
      (   H = move(R) -> doMove(R,S,S0) %Move
      ;   H = winTheGame -> (touchdown(R,S0), doMove(R,SI,S0), S = do(putBall, SI)) %Move and then putBall
      ;   H = pass(R) -> (onFieldWithHuman(S0), doMove(R,SI,S0), S = do(passBall, SI)) % pass the ball to a human in the same field
      ;   H = forward -> S = do(forward, S0) %Does Forward
      ;   H = left -> S = do(left, S0) %Turns Left
      ;   H = right -> S = do(right, S0) %Turns Right
      ;   H = putBall -> S = do(putBall, S0) %Puts ball on field
      ;   H = throwBall -> S = do(throwBall, S0) %Throw ball
      ;   H = giveUp -> S = do(giveUp, S0) % Stops searching, no solution found
      ;   H = passBall -> S = do(passBall,S0) % passes ball to the human in same field
      ).
  
  
  run30Times(N0, NF) :-
      runManyMaps(N0,NF).
  
  
  seq(From,_,From).
  seq(From,To,X) :-
      From<To,
      Next is From+1,
      seq(Next,To,X).
  
  loop(NWorld) :-
      seq(1,10,_),
      runManyMaps(NWorld,NWorld),
      fail.
  loop.
  
  %Removes all objects from world
  clearWorld :-
      retractall(w_Wall(_)),
      retractall(w_Touchdown(_)),
      retractall(w_Human(_)),
      retractall(w_Orc(_)).
  
  %Clears and builds 4x4 world
  recreateWorld(N) :-
      clearWorld,
      build4x4Walls,
      buildWorld(N).
  
  %Builds 4x4 outer walls to limit world
  build4x4Walls :-
      % left walls
      asserta(w_Wall(r(0,0))),
      asserta(w_Wall(r(0,1))),
      asserta(w_Wall(r(0,2))),
      asserta(w_Wall(r(0,3))),
      asserta(w_Wall(r(0,4))),
      asserta(w_Wall(r(0,5))),
      asserta(w_Wall(r(0,6))),
      
      % right walls
      asserta(w_Wall(r(6,0))),
      asserta(w_Wall(r(6,1))),
      asserta(w_Wall(r(6,2))),
      asserta(w_Wall(r(6,3))),
      asserta(w_Wall(r(6,4))),
      asserta(w_Wall(r(6,5))),
      asserta(w_Wall(r(6,6))),

      % top walls
      asserta(w_Wall(r(1,6))),
      asserta(w_Wall(r(2,6))),
      asserta(w_Wall(r(3,6))),
      asserta(w_Wall(r(4,6))),
      asserta(w_Wall(r(5,6))),
  
      % bottom walls
      asserta(w_Wall(r(1,0))),
      asserta(w_Wall(r(2,0))),
      asserta(w_Wall(r(3,0))),
      asserta(w_Wall(r(4,0))),
      asserta(w_Wall(r(5,0))),
      asserta(w_Wall(r(6,0))).
  
    buildWorld(1) :-
        asserta(w_Touchdown(r(2,3))),
        asserta(w_Human(r(1,5))),
        asserta(w_Orc(r(1,3))),
        asserta(w_Orc(r(2,4))),
        asserta(w_Orc(r(3,3))).
    
    
    buildWorld(2) :-
        asserta(w_Touchdown(r(4,3))),
        asserta(w_Orc(r(3,1))),
        asserta(w_Orc(r(3,2))),
        asserta(w_Orc(r(3,3))),
        asserta(w_Orc(r(2,3))),
        asserta(w_Orc(r(2,1))).
    
    buildWorld(3) :-
        asserta(w_Touchdown(r(3,3))).
    
    
    buildWorld(4) :-
        asserta(w_Touchdown(r(4,3))),
        asserta(w_Human(r(1,3))),
        asserta(w_Orc(r(3,1))),
        asserta(w_Orc(r(3,2))),
        asserta(w_Orc(r(3,3))),
        asserta(w_Orc(r(2,3))),
        asserta(w_Orc(r(1,3))).
    
    buildWorld(5) :-
        asserta(w_Human(r(2,1))),
        asserta(w_Human(r(2,2))),
        asserta(w_Human(r(1,3))),
        asserta(w_Touchdown(r(2,3))),
        asserta(w_Human(r(1,2))).
    
    buildWorld(6) :-
        asserta(w_Human(r(1,3))),
        asserta(w_Touchdown(r(2,3))).
    
    buildWorld(7) :-
        asserta(w_Touchdown(r(1,3))),
        asserta(w_Touchdown(r(2,2))).
  
  
  runManyMaps(N0,NF) :- %Runs map N0 until NF inclusive in sequence.
      consult('fieldBuilder.pl'), %This file has information for different maps
      
      
      make, %Reset files if changed
      runInSequence(N0,NF). %Runs many maps in sequence
  
  run :-
      %consult('fieldBuilder.pl'), %This file has information for different maps
      run(1).
  
  
  runInSequence(N0,NF) :- %This loops through different maps and runs agent in each one
      run(N0),
      N1 is N0+1,
      (N1 =< NF -> runInSequence(N1,NF) ; true). %Run next map if not done.
  
  run(N) :-
      recreateWorld(N),
      format('~n~n~n   Playing on world ~d ~n~n~n', N),
      callTime(runloop(0,s0)).
  
  runloop(T,_) :-
      maxNumberOfExploredFields(Max),
      T >= Max,
      write('Reached max number of moves, player get lost :c'), !, false.
  
  %Main loop.
  runloop(T,S0) :-
      %Gets current ballPlayer position and prints.
      ballPlayer(r(X,Y),D,S0),
      format('Ball at [~d,~d, ~w], ', [X,Y,D]),!,
  
      %Get action from heuristic (Strategy) in this situation
      heuristic(S0,H),
      format('wants to do ~w, ', [H]), %Prints desired action
  
      %Calls actuators which use planning to do Actions
      doActions(H,S,S0),
      write('does '),
      planToActionList(S,S0,[],L),
      printList(L), %Prints list of all smaller actions that were done.
      format('~n'),
  
      NT is T+1, %Set new timestep
  
      %The following are needed to check if ballPlayer climbed out of the cave
      do(A,_) = S, %Get last action done
      ballPlayer(_,_,S), %Get balls position now
  
      (   ((A = putBall ; A = giveUp) ; \+ballInGame(S)) -> endLoop(S,A)
      ;   (!,runloop(NT,S))
      ),!.
  
  endLoop(S,_) :-
      countActions(S,s0,N),
      format('~n~n   '),
      (reachedTouchdown(S) -> write('Reached the touchdown'); write('Could not find touchdown')),
      format(' in a total of ~d actions! ~n~n',N).
  
  
  % HELPERS
  % These are the utility functions that are used inside the heuristic and 
  % planning functions to enhance the code readability 
  
  add(E,L,[E|L]). %Adds element to list
  
  countList([],0). %Counts number of elements in list
  countList([_|Tail], N) :- countList(Tail, N1), N is N1 + 1.
  
  % These functions form the lists of visited/not visited/adjacent fields
  % These lists are needed to make a decicion where to go next
  trimNotVisited([],_,[]). %Removes Fields that weren't visited from list of Fields
  trimNotVisited([H|T],S,LT) :- trimNotVisited(T,S,L), (visited(H,S) -> append([H],L,LT); LT = L).
  trimVisited([],_,[]). %Removes Fields that were visited from list of Fields
  trimVisited([H|T],S,LT) :- trimVisited(T,S,L), (visited(H,S) -> LT = L; append([H],L,LT)).
  trimNotAdjacent([],_,[]). 
  trimNotAdjacent(_,[],[]). %Removes Fields from List L that are no adjacent to any Field in list T
  trimNotAdjacent([LAH|LAT],[TH|TT],LT) :-
      trimNotAdjacent([LAH],TT,LT1),
      trimNotAdjacent(LAT,[TH|TT],LT2),
      append(LT1,LT2,LT3),
      (isAdjacent(LAH,TH) -> append([LAH],LT3,LT) ; LT = LT3).
  
  %Converts plan (Actions from one situation to another) to Action list
  planToActionList(S,S,ACC,ACC).
  planToActionList(do(A,S1),S0,ACC,X) :- planToActionList(S1,S0,[A|ACC],X).
  
  %Prints List
  printList([]).
  printList([A|B]) :-
      format('~w, ', A),
      printList(B).
  
  %Returns Field in front of another in a certain direction
  getForwardField(r(X0,Y0),D0,r(XN,YN)) :-
      (D0 = n, XN is X0, YN is Y0+1);
      (D0 = e, XN is X0+1, YN is Y0);
      (D0 = s, XN is X0, YN is Y0-1);
      (D0 = w, XN is X0-1, YN is Y0).
  
  
  %Checks if one Field is adjacent to another Field
  isAdjacent(r(X,Y),r(XT,YT)) :-
      (X =:= XT, Y =:= YT+1);
      (X =:= XT, Y =:= YT-1);
      (X =:= XT+1, Y =:= YT);
      (X =:= XT-1, Y =:= YT).
  
  %Checks if a ballPlayer in Field r(X,Y), 
  %looking to Direction D 
  %is facing Field r(XT,YT)
  isFacing(r(X,Y),D,r(XT,YT)) :-
      (D = n, X =:= XT, YT > Y);
      (D = s, X =:= XT, YT < Y);
      (D = e, Y =:= YT, XT > X);
      (D = w, Y =:= YT, XT < X).
  
  %Returns list of all adjacent Fields to the fields in L
  getAdjacentFields(r(X,Y),L) :-
      XL is X-1,
      XR is X+1,
      YD is Y-1,
      YU is Y+1,
      append([r(XL,Y), r(XR,Y), r(X,YU), r(X,YD)],[],L).
  
  % Return the list of all fields that are adjacent to any of the visited 
  % fields but are not visited yet
  getAllExplorableFields(S,L) :- getAllExplorableFields(S,S,L). %Simplifies call
  getAllExplorableFields(S,s0,L) :-
      ballPlayer(R,_,s0),
      getAdjacentFields(R,LA),
      appendWithExplorableCheck(LA,S,[],L).
  getAllExplorableFields(S,do(A,S0),L) :-
      getAllExplorableFields(S,S0,L0),
      ballPlayer(R,_,do(A,S0)),
      getAdjacentFields(R,LA),
      appendWithExplorableCheck(LA,S,L0,L).
  
  appendWithExplorableCheck([],_,L2,L2).
  appendWithExplorableCheck([H|T],S,L2,L) :-
      appendWithExplorableCheck(T,S,L2,LT),
      (   isExplorable(H,S,LT) -> L = [H|LT] ; L = LT).
  
  isExplorable(R,S,L) :- \+member(R,L), \+visited(R,S).
  %the field is explorable if it not visited yet and 
  % not present in Explorable list yet (to avoid dublicates)
  
  %Counts number of actions between two situations
  countActions(s0,s0,0).
  countActions(S,S,0).
  countActions(do(A,S),S0,N) :- 
      ((A = forward ; A = throwBall), countActions(S,S0,N0), N is N0+1);
      (A = passBall, countActions(S,S0,N0), N is N0-1);
      ((A \= forward, A \= passBall), countActions(S,S0,N0), N is N0 ).
  
  callTime(G,T) :- %Returns Call Time
      statistics(runtime,[T0|_]),
      G,
      statistics(runtime,[T1|_]),
      T is T1 - T0.
  
  callTime(G) :- %Prints Call Time
      callTime(G,T),
      format('~n~n[Time to run in ms: ~d]',T).
  
  