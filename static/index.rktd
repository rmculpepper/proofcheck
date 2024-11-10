(html
 (head (title "Proof Checker")

       (meta ([charset "utf-8"]))
       (link ([href "main.css"]
              [rel "stylesheet"]
              [type "text/css"]))

       #;
       ;; Handlebars via CDN ( https://cdnjs.com/libraries/handlebars.js )
       (script ([src "https://cdnjs.cloudflare.com/ajax/libs/handlebars.js/4.7.8/handlebars.min.js"]
                [integrity "sha512-E1dSFxg+wsfJ4HKjutk/WaCzK7S2wv1POn1RRPGh8ZK+ag9l244Vqxji3r6wgz9YBf6+vhQEYJZpSjqWFPg9gg=="]
                [crossorigin "anonymous"]
                [referrerpolicy "no-referrer"]))

       ;; jQuery via CDN ( https://releases.jquery.com/ )
       (script ([src "https://code.jquery.com/jquery-3.7.1.min.js"]
                [integrity "sha256-/JqT3SQfawRcv/BIHPThkBvs0OEvtFFmqPF/lYI/Cxo="]
                [crossorigin "anonymous"]))

       (script ([src "main.js"]
                [type "text/javascript"]))

       #|/head|#)

 (body

  (div ([class "main_area"])
       (h1 "Proof Checker")

       (p ([class "warning"])
          "Make sure to save your work often to an external editor. " (br)
          "Reloading this page may clear the proof text.")

       (div ([id "proof_area"])
            (h2 "Proof")

            (p "The proof checker knows the axioms from Homework 6. "
               "You can also declare your own axioms for experimentation. "
               "See the axiom list and example under Documentation.")

            (div () (label ([for "prooftext"]) "Proof"))
            (div ()
                 (textarea ([id "prooftext"]
                            [rows "20"]
                            [cols "80"]
                            [maxlength "100000"]
                            [spellcheck "false"]
                            [placeholder "Enter your proof here."])))
            (div ()
                 (button ([id "checkproof"] [type "button"])
                         "Check proof")))

       (div ([id "output_area"] [style "display: none"])
            (h2 "Output")

            (div ([id "wait_for_server"] [class "waiting"] [style "display: none"])
                 (div ([class "par"]) "Waiting for the server to respond."))

            (div ([id "out_of_date"] [class "outdated"] [style "display: none"])
                 (div ([class "par"])
                      "The proof has changed since it was last checked, " (br)
                      "so this output may be out of date."))

            (div ([id "output_inner_area"]))

            #|/div:output|#)

       (div ([id "docs_area"])
            (h2 "Documentation")

            (p "The proof checker supports the following symbols and reserved words. "
               "Reserved words and identifiers are " (em "case sensitive") ".")

            (div (em "Logic and Arithmetic: ")
                 (pre "¬ not ∧ and ∨ or ⇒ implies ⇔ iff ∀ forall ∃ exists "
                      "∈ in ℕ NN "
                      "+ * ="))
            (div (em "Justifications: ")
                 (div (pre "∧Intro ∧ElimL ∧ElimR AndIntro AndElimL AndElimR"))
                 (div (pre "∨IntroL ∨IntroR ∨Elim OrIntroL OrIntroR OrElim"))
                 (div (pre "⇒Elim ⇒Intro ImpliesElim ImpliesIntro "
                      "ImplicationElim ImplicationIntro"))
                 (div (pre "⇔ElimF ⇔ElimB ⇔Intro IffElimF IffElimB IffIntro"))
                 (div (pre "∀Elim ∀Intro ForAllElim ForAllIntro"))
                 (div (pre "∃Elim ∃Intro ExistsElim ExistsIntro"))
                 (div (pre "ModusTollens Contradiction Algebra"))
                 (div (pre "↦ :-> ⇒ forward fwd ⇐ backward bwd")))

            (p "Literal objects (aka constants) are written as identifiers "
               "between single quotes: for example, " (tt "'Mouse'") ".")

            (p "The proof checker does not check algebra. "
               "The proof checker does not check set membership, "
               "such as for ∀Elim and ∃Intro rules.")

            (h3 "Homework 6 Axioms")

            (div ([class "axioms"])
                 (pre "
Axiom 1: Small('Mouse')
Axiom 2: Brave('Lion')
Axiom 3: ∀a,b ∈ A, Fears(a,b) ⇒ ¬Fears(b,a)
Axiom 4: ∀a,b ∈ A, Small(a) ⇒ Brave(b) ⇒ Fears(a,b)
Axiom 5: ∀n ∈ NN, Even(n) ⇔ (∃ k ∈ NN, n = 2*k)
Axiom 6: ∀n ∈ NN, Odd(n) ⇔ (∃ k ∈ NN, n = 2*k + 1)
Axiom 7: ∀n ∈ NN, Even(n) ∨ Odd(n)
Axiom 8: ∀d,n ∈ NN, Divides(d,n) ⇔ (∃ k ∈ NN, n = k*d)
Axiom 9: ∀n ∈ NN, Composite(n) ⇔ (∃ d ∈ NN, lt(1, d) ∧ lt(d, n) ∧ Divides(d, n))
Axiom 10: ∀n,d,q,r ∈ NN, Div(n,d,q,r) ⇔ (n = q*d + r ∧ le(0, r) ∧ lt(r, d))
Axiom 11: ∀n,d,q1,r1,q2,r2 ∈ NN, Div(n,d,q1,r1) ⇒ Div(n,d,q2,r2) ⇒ (q1 = q2) ∧ (r1 = r2)
"))

            (h3 "Example: Implication")

            (div ([class "example"])
                 (pre "
Axiom 1: Tue implies CS220
Axiom 2: Thu implies CS220
Axiom 3: CS220 implies Happy

1 Block
  1.1 Assume Tue
  1.2 Want Happy
  1.3 Derive CS220 by ImpliesElim on Axiom 1, #1.1
  1.4 Derive Happy by ImpliesElim on Axiom 3, #1.3
2 Derive Tue implies Happy by ImpliesIntro on #1
"))

            (h3 "Example: Disjunction")

            (div ([class "example"])
                 (pre "
Axiom 1: sun implies (bike and garden)
Axiom 2: rain implies clean

1 Block
  1.1 Assume sun or rain
  1.2 Want garden or clean
  1.4 Block
    1.4.1 Assume sun
    1.4.2 Want garden or clean
    1.4.3 Derive bike and garden by ImpliesElim on Axiom 1, #1.4.1
    1.4.4 Derive garden by AndElimR on #1.4.3
    1.4.5 Derive garden or clean by OrIntroL on #1.4.4
  1.5 Derive sun implies (garden or clean) by ImpliesIntro on #1.4
  1.6 Block
    1.6.1 Assume rain
    1.6.2 Want garden or clean
    1.6.3 Derive clean by ImpliesElim on Axiom 2, #1.6.1
    1.6.4 Derive garden or clean by OrIntroR on #1.6.3
  1.7 Derive rain implies (garden or clean) by ImpliesIntro on #1.6
  1.8 Derive garden or clean by OrElim on #1.1, #1.5, #1.
2 Derive (sun or rain) implies (garden or clean) by ImpliesIntro on #1
"))

            (h3 "Example: Universal")

            (div ([class "example"])
                 (pre "
Axiom 1: Small('Mouse')
Axiom 2: Brave('Lion')
Axiom 3: forall a,b in A, (Small(a) and Brave(b)) implies Fears(a,b)

1 Derive Small('Mouse') and Brave('Lion')
  by AndIntro on Axiom 1, Axiom 2
2 Derive (Small('Mouse') and Brave('Lion')) implies Fears('Mouse', 'Lion')
  by ForAllElim on Axiom 3 with a,b :-> 'Mouse', 'Lion'
3 Derive Fears('Mouse', 'Lion')
  by ImpliesElim on #2, #1
"))

            (h3 "Example: Existentials, Algebra")

            (div ([class "example"])
                 (pre "
Axiom 1: forall n in NN, Even(n) iff (exists k in NN, n = 2*k)
Axiom 2: forall n in NN, Odd(n) iff (exists k in NN, n = 2*k+1)

1 Block
  1.1 Intro n in NN
  1.2 Assume Odd(n)
  1.3 Want Even(n+1)
  1.4 Derive exists k in NN, n = 2*k+1 
      by Axiom 2; with n :-> n; forward; on #1.2
  1.5 Block
    1.5.1 Intro m in NN
    1.5.2 Assume n = 2*m+1
    1.5.3 Derive n+1 = 2*(m+1) by Algebra on #1.5.2
    1.5.4 Derive exists k in NN, n+1 = 2*k
          by ExistsIntro on #1.5.3 with k :-> m+1
    1.5.5 Derive Even(n+1)
          by Axiom 1; with n :-> n+1; backward; on #1.5.4
  1.6 Derive Even(n+1)
      by ExistsElim on #1.4, #1.5
2 Derive forall n in NN, Odd(n) implies Even(n+1)
  by #1
"))

            (h3 "Example: Contradiction")

            (div ([class "example"])
                 (pre "
1 Block
  1.1 Assume not A
  1.2 Want not (A and B)
  1.3 Block
    1.3.1 Assume A and B
    1.3.2 Want A and not A
    1.3.3 Derive A by AndElimL on #1.3.1
    1.3.4 Derive A and not A by AndIntro on #1.3.3, #1.1
  1.4 Derive not (A and B) by Contradiction on #1.3
2 Derive not A implies not (A and B) by ImpliesIntro on #1
"))

            #|/div:docs|#))

  (script "initialize();")))
