(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.Rtopology.
From Stdlib Require Import Classical.
From Stdlib Require Import Classical_Pred_Type.
From Stdlib Require Import Lra.

From Waterproof Require Import Tactics.
From Waterproof Require Import Automation.
From Waterproof Require Import Notations.Common.
From Waterproof Require Import Notations.Reals.
From Waterproof Require Import Notations.Sets.
From Waterproof Require Import Chains.
From Waterproof Require Import Libs.Analysis.SupAndInf.
From Waterproof Require Import Libs.Analysis.OpenAndClosed.
From Waterproof Require Import Libs.Analysis.LimsupLiminfBolzano.
From Waterproof Require Import Libs.Analysis.Subsequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

(** * Limit points of sets

A point x is a limit point (accumulation point) of A if every open ball
around x contains a point of A different from x.
*)

Definition is_limit_point_of (x : ℝ) (A : subset ℝ) : Prop :=
  ∀ ε > 0, ∃ y ∈ A, 0 < | y - x | < ε.

Notation "x 'is' 'a' '_limit' 'point_' 'of' A" :=
  (is_limit_point_of x A) (at level 69).

Notation "x 'is' 'a' 'limit' 'point' 'of' A" :=
  (is_limit_point_of x A) (at level 69, only parsing).

Waterproof Register Expand "limit" "point";
  for is_limit_point_of;
  as "Definition limit point".

(** * Compactness (Stdlib API)

We use the Stdlib's notion of compactness: every open cover has a finite subcover.
See [Reals.Rtopology] in the Stdlib for the full definition and API.

Key facts available from the Stdlib (usable in proofs):
  - [compact_P3]: the closed interval [a,b] is compact.
  - [compact_P5]: closed + bounded implies compact.
  - [compact_P2]: compact implies closed.
  - [compact_P1]: compact implies bounded.
*)

Definition is_compact (A : subset ℝ) : Prop := compact A.

Notation "A 'is' '_compact_'" := (is_compact A) (at level 69).
Notation "A 'is' 'compact'" := (is_compact A) (at level 69, only parsing).

(** Heine-Borel: [a, b] is compact. *)
Lemma segment_is_compact (a b : ℝ) :
    is_compact (fun x => (a <= x /\ x <= b)).
Proof.
  unfold is_compact. apply compact_P3.
Qed.

(** * Bounded injective sequences and limit points

Every bounded infinite set has a limit point (Bolzano-Weierstrass route).
*)

(** A sequence (a_n) gives infinitely many distinct points in A if it is
    injective and contained in A. *)
Definition inj_seq_in (A : subset ℝ) (a : ℕ → ℝ) : Prop :=
  (forall n : ℕ, a n ∈ A) /\
  (forall n m : ℕ, (n <> m)%nat -> a n <> a m).

(** If (a_n) is a bounded injective sequence in A, then A has a limit point.

    Proof: Bolzano-Weierstrass gives a convergent subsequence a_{phi(k)} -> x.
    Then x is a limit point of A: every ball around x contains infinitely many
    terms a_{phi(k)}, all distinct from each other, and all in A.
*)
Theorem inj_bounded_seq_has_limit_point
    (A : subset ℝ) (a : ℕ → ℝ) :
  inj_seq_in A a →
  has_ub a →
  has_lb a →
  ∃ x ∈ ℝ, x is a _limit point_ of A.
Proof.
  intros [Ha_A Ha_inj] Hub Hlb.
  assert (has_ub a ⇒ (has_lb a ⇒
    ∃ (phi : ℕ → ℕ), ∃ (x : ℝ), is_index_seq phi ∧
      converges_to (fun k ↦ a (phi k)) x)) as HBW.
  { apply Bolzano_Weierstrass. }
  destruct (HBW Hub Hlb) as [phi [x [Hphi_idx Hphi_cv]]].
  exists x. split. { apply mem_subset_full_set. }
  intros ε Hε.
  assert (ε / 2 > 0) as Hε2.
  { apply Rdiv_lt_0_compat.
    - exact Hε.
    - apply Rlt_0_2. }
  destruct (Hphi_cv (ε / 2) Hε2) as [M [_ HM]].
  assert (phi M < phi (S M))%nat as Hphi_str.
  { apply Hphi_idx.
    exact (mem_subset_full_set M). }
  assert (phi M <> phi (S M)) as Hphi_ne.
  { exact (Nat.lt_neq _ _ Hphi_str). }
  assert (a (phi M) <> a (phi (S M))) as Ha_ne.
  { apply Ha_inj. exact Hphi_ne. }
  destruct (classic (a (phi M) = x)) as [Heq | Hne].
  - exists (a (phi (S M))). split.
    + apply Ha_A.
    + split.
      * apply Rabs_pos_lt.
        intro Heq2. apply Ha_ne.
        rewrite Heq. symmetry.
        exact (Rminus_diag_uniq _ _ Heq2).
      * apply (Rlt_trans _ (ε / 2) _).
        -- exact (HM (S M) (Nat.le_succ_diag_r _)).
        -- ltac1:(lra).
  - exists (a (phi M)). split.
    + apply Ha_A.
    + split.
      * apply Rabs_pos_lt.
        intro Heq2. apply Hne.
        exact (Rminus_diag_uniq _ _ Heq2).
      * apply (Rlt_trans _ (ε / 2) _).
        -- exact (HM M (Nat.le_refl _)).
        -- ltac1:(lra).
Qed.

Close Scope subset_scope.
Close Scope R_scope.
