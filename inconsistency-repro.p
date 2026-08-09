%------------------------------------------------------------------------------
% Minimal reproduction of the Curry/Russell paradox that CoqHammer's
% (extraction-branch) untyped FOL translation reintroduces when definitional
% axioms are emitted WITHOUT closure/lambda type guards.
%
% Symbols mirror the real generated problem (renamed for readability):
%   ap(F,X)        -- untyped application, the real encoding's happ(F,X)
%   p(X)           -- "the Prop-coded object X holds", the real encoding's p(.)
%   proper         -- Corelib.Classes.Morphisms.Proper       (a constant)
%   lam            -- the anonymous lambda Proper unfolds to  ($_lam_NN)
%   comp           -- Corelib.Classes.RelationClasses.complement (a constant)
%   lam_hold/3     -- reified truth of (lam @ A @ R @ m)      (lam___$aN)
%   comp_hold/4    -- reified truth of (comp @ A @ R @ x @ y) (complement___$aN)
%   false          -- Coq's False
%
% Run:  eprover --auto --tstp-format curry_repro.p
% Expect: SZS status ContradictoryAxioms  (the AXIOMS ALONE are inconsistent;
%         there is no conjecture).
%------------------------------------------------------------------------------

% Proper is *defined* to be the diagonal lambda:  Proper A R m := R m m.
% (1) the definitional equality of the two head constants  [$_def_Proper]
fof(def_proper, axiom, proper = lam).

% (2) the lambda body:  lam A R m  <=>  R m m   (R applied reflexively at m)
%     [$_lam_NN]
fof(lam_body, axiom,
    ![A,R,M]: ( lam_hold(A,R,M) <=> p(ap(ap(R,M),M)) )).

% (3) link the applied form to the reified predicate  [$adef_lam_NN_$a3]
fof(lam_applied, axiom,
    ![A,R,M]: ( p(ap(ap(ap(lam,A),R),M)) <=> lam_hold(A,R,M) )).

% complement A R x y := R x y -> False.   [$_def_complement]
fof(def_complement, axiom,
    ![A,R,X,Y]: ( comp_hold(A,R,X,Y) <=> ( p(ap(ap(R,X),Y)) => p(false) ) )).

% link the applied form to the reified predicate  [$adef_complement_$a4]
fof(comp_applied, axiom,
    ![A,R,X,Y]: ( p(ap(ap(ap(ap(comp,A),R),X),Y)) <=> comp_hold(A,R,X,Y) )).

% Coq's False is uninhabited: it is not provable.  [_HAMMER_COQ_FALSE]
fof(no_false, axiom, ~ p(false)).

%------------------------------------------------------------------------------
% None of these axioms carries a type guard on A,R,x,y, so they hold for EVERY
% first-order term -- including ill-typed self-applications where a relation is
% fed to itself.  That is exactly Curry's paradox, and the six axioms above are
% jointly unsatisfiable.
%------------------------------------------------------------------------------
