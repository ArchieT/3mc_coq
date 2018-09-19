Inductive Color : Set := White | Gray | Black.
Definition next (c:Color) := match c with
    | White => Gray
    | Gray => Black
    | Black => White 
end.
Variable prev : Color -> Color.
Axiom defining_prev : 
    forall c : Color, (next (prev c)) = c.
(* Definition prev (c:Color) := match c with
    | White => Black
    | Gray => White
    | Black => Gray
end. *)
Lemma next_three_times 
    : forall c : Color, (next (next (next c))) = c.
Proof. Admitted.
Lemma prev_three_times 
    : forall c : Color, (prev (prev (prev c))) = c.
Proof. Admitted.
Lemma next_of_prev_is_orig : 
    forall c : Color, (next (prev c)) = c.
Proof. Admitted.
Lemma prev_of_next_is_orig : forall c : Color, (prev (next c)) = c.
Proof. Admitted.
Inductive RankHalf : Set := Outer | Inner.
Inductive Rank : Set := 
    | Most (_:RankHalf)
    | Second (_:RankHalf)
    | Middle (_:RankHalf).
Definition inw (r:Rank) : Rank := match r with
    | Most Outer => Second Outer
    | Second Outer => Middle Outer
    | Middle Outer => Middle Inner
    | Middle Inner => Second Inner
    | Second Inner => Most Inner
    | Most Inner => Most Inner
end.
Inductive OutRank : Set := Outboard | Onboard (r:Rank).
Variable out : Rank -> OutRank.
Axiom out_mostouter : (out (Most Outer)) = Outboard.
Axiom out_never_same : forall a : Rank, (out a) <> (Onboard a).
Axiom out_if_inw : 
    forall a : Rank, forall b : Rank, 
    (a = (inw b)) -> ((Onboard b) = (out a)).
Inductive SegmentHalf : Set := FirstHalf | SecondHalf.
Definition SegmentEight : Set := SegmentHalf * SegmentHalf * SegmentHalf.
Definition ColorSegment : Set := Color.
Definition File : Set := ColorSegment * SegmentEight.
(* Definition oneFilePluswards (f:File) : File := *)
Inductive Count : Set := Once | OnceMore (than:Count).
Inductive Natural : Set := Zero | Positive (c:Count).
Variable filePlus : File -> Count -> File.
Variable fileMinus : File -> Count -> File.
Axiom fileminus_on_fileplus :
    forall f : File,
    forall c : Count,
    (fileMinus (filePlus f c) c) = f.
Axiom fileplus_on_fileminus :
    forall f : File,
    forall c : Count,
    (filePlus (fileMinus f c) c) = f.
Axiom fileplus_one_last_in_color :
    forall c : Color,
    (filePlus (c, (SecondHalf, SecondHalf, SecondHalf)) Once) = (next c, (FirstHalf, FirstHalf, FirstHalf)).
Lemma fileminus_one_last_in_color :
    forall c : Color,
    (fileMinus (c, (FirstHalf, FirstHalf, FirstHalf)) Once) = (prev c, (SecondHalf, SecondHalf, SecondHalf)).
Proof. Admitted.
Axiom fileplus_firsteight :
    forall c : Color,
    forall a : SegmentHalf,
    forall b : SegmentHalf,
    (filePlus (c, (a, b, FirstHalf)) Once) = (c, (a, b, SecondHalf)).
Axiom fileplus_firstquarter :
    forall c : Color,
    forall a : SegmentHalf,
    (filePlus (c, (a, FirstHalf, SecondHalf)) Once) = (c, (a, SecondHalf, FirstHalf)).
Axiom fileplus_firsthalf :
    forall c : Color,
    (filePlus (c, (FirstHalf, SecondHalf, SecondHalf)) Once) = (c, (SecondHalf, FirstHalf, FirstHalf)).
Axiom fileplus_more_than_once :
    forall f : File,
    forall c : Count,
    (filePlus f (OnceMore c)) = filePlus (filePlus f Once) c.