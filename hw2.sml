(* Dan Grossman, Coursera PL, HW2 Provided Code *)

(* if you use this function to compare two strings (returns true if the same
   string), then you avoid several of the functions in problem 1 having
   polymorphic types that may be confusing *)
fun same_string(s1 : string, s2 : string) =
    s1 = s2

fun all_except_option (s : string, slist : string list) =
    let fun helper (slist : string list, acc : string list) =
	    case (slist, acc) of
		([], _) => NONE
	      | (x::xs, ys) => if same_string(x, s)
			       then SOME (ys@xs)
			       else helper(xs, x::ys)
    in
	helper(slist, [])
    end

fun get_substitutions1 (substitutions : string list list, s : string) =
    case substitutions of
	[] => []
      | x::xs => let val substitutions_rest = get_substitutions1(xs, s)
		 in
		     case all_except_option (s, x) of
			 NONE => substitutions_rest
		       | SOME ys => ys@substitutions_rest
		 end
		     
	    
fun get_substitutions2 (substitutions : string list list, s : string) =
    let fun helper (substitutions : string list list, acc : string list) =
	    case substitutions of
		[] => acc
	      | x::xs => case all_except_option (s,x) of
			     NONE => helper (xs,acc)
			   | SOME ys => helper (xs, ys@acc)
    in
	helper(substitutions, [])
    end

fun similar_names (substitutions : string list list, {first=f, middle=m, last=l}) =
    let val nicknames = get_substitutions2(substitutions, f)
	fun helper (nicknames, new_full_names) =
	    case nicknames of
		[] => {first=f, middle=m, last=l}::new_full_names
	      | x::xs => helper(xs, {first=x, middle=m, last=l}::new_full_names)
    in
	helper(nicknames, [])
    end

(* you may assume that Num is always used with values 2, 3, ..., 10
   though it will not really come up *)
datatype suit = Clubs | Diamonds | Hearts | Spades
datatype rank = Jack | Queen | King | Ace | Num of int 
type card = suit * rank

datatype color = Red | Black
datatype move = Discard of card | Draw 

exception IllegalMove

(* put your solutions for problem 2 here *)

fun card_color (suit, rank) =
    case suit of
	Spades => Black
      | Clubs => Black
      | Diamonds => Red
      | Hearts => Red

fun card_value (suit, rank) =
    case rank of
	Num x => x
      | Ace => 11
      | _ => 10

fun remove_card (cs, c, e) =
    let fun helper (cs, new_cs) =
	    case cs of
		[] => raise e
	      | x::xs => if x = c then new_cs@xs else helper(xs, x::new_cs)
    in
	helper(cs, [])
    end
	
fun all_same_color cs =
    case cs of
	[] => true
      | _::[] => true
      | (Clubs,_)::((s,r)::rest) => (s = Spades orelse s = Clubs) andalso (all_same_color((s,r)::rest))
      | (Spades,_)::((s,r)::rest) => (s = Spades orelse s = Clubs) andalso (all_same_color((s,r)::rest))
      | (Diamonds,_)::((s,r)::rest) => (s = Diamonds orelse s = Hearts) andalso (all_same_color((s,r)::rest))
      | (Hearts,_)::((s,r)::rest) => (s = Diamonds orelse s = Hearts) andalso (all_same_color((s,r)::rest))
					   
fun sum_cards cs =
    let fun helper(cs, sum) =
	    case cs of
		[] => sum
	      | c::cs' => helper(cs', card_value(c)+sum)
    in
	helper(cs, 0)
    end
	
fun score (cards_held, goal) =
    let val sum = sum_cards(cards_held)
	val is_same_color = all_same_color(cards_held)
	val prelim_score = if sum > goal then 3*(sum - goal) else goal-sum
    in
	if is_same_color then prelim_score div 2 else prelim_score
    end
 	
fun officiate (card_list, moves, goal) =
    let fun helper (card_list, cards_held, moves, current_score) =
	    case ( moves, card_list ) of
		( [],_ ) => current_score
	      | ( (Discard card)::ms, _) => let val new_cards_held = remove_card(cards_held, card, IllegalMove)
					    in helper(card_list, new_cards_held, ms, score(new_cards_held, goal)) end
	      | ( (Draw)::ms, [] ) => current_score
	      | ( (Draw)::ms, c::cs) => let val new_sum = sum_cards(c::cards_held)
					in if new_sum >= goal
					   then score(c::cards_held, goal)
					   else helper(cs, c::cards_held, ms, score(c::cards_held, goal))
					end
    in
	helper(card_list, [], moves, 0)
    end

fun score_challenge (cards_held, sum_cards, goal) =
    let val is_same_color = all_same_color(cards_held)
	val prelim_score = if sum_cards > goal then 3*(sum_cards - goal) else goal-sum_cards
    in
	if is_same_color then prelim_score div 2 else prelim_score
    end

fun officiate_challenge (card_list, moves, goal) =
    let fun helper (card_list, cards_held, moves, current_score) =
	    case ( moves, card_list ) of
		( [],_ ) => current_score
	      | ( (Discard (suit, rank))::ms, _) => let val new_cards_held = remove_card(cards_held, (suit, rank), IllegalMove)
							val is_ace = rank = Ace
						    in
							if is_ace
							then helper(card_list, new_cards_held, ms, score_challenge(new_cards_held, sum_cards(cards_held) - 1, goal))
							else helper(card_list, new_cards_held, ms, score(new_cards_held, goal))
						    end
	      | ( (Draw)::ms, [] ) => current_score
	      | ( (Draw)::ms, (suit, rank)::cs) => let val is_ace = rank = Ace
						       val new_sum = if is_ace then sum_cards(cards_held) + 1 else sum_cards(cards_held) + card_value((suit, rank))
						   in
						       if is_ace andalso new_sum + 10 < goal
						       then helper (cs, (suit, rank)::cards_held, ms, score_challenge((suit, rank)::cards_held, new_sum+10, goal))
						       else if new_sum < goal
						       then helper(cs, (suit, rank)::cards_held, ms, score_challenge((suit, rank)::cards_held, new_sum, goal))
						       else score_challenge((suit, rank)::cards_held, new_sum, goal)
						   end
    in
	helper(card_list, [], moves, 0)
    end

fun careful_player (card_list, goal) =
    let fun helper (card_list, cards_held, current_score) =
	    case (card_list, cards_held, current_score) of
		(_, _, 0) => []
	      | ([], _, _) => []
	      | (c::cs, _, _) => if ( sum_cards(cards_held + 10 < goal)) then Draw::helper(cs, c::cards_held, score(c::cards_held)) else []
	      | (c::cs, d::ds, _) => if ( sum_cards(c::cards_held) > goal) then (Discard d)::helper(card_list, ds, score(ds, goal))
				     else
 			 
    in
	helper(card_list, [], 0)
    end
