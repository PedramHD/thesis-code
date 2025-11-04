/// SerializationHelpers
/// ====================
///
/// This module provides a small set of helper functions to implement serializing/parsing of
/// messages and sessions. While the single functions can be used stand-alone, the intended use of
/// this module is to call ``labeled_crypto_funs`` once and use the functions from the result of
/// that call.
///
/// All implementations are "open" on purpose, so F* can reason about these functions in the context
/// of :doc:`LabeledCryptoAPI` (instead of being limited to the functions within here).
module SerializationHelpers

open SecrecyLabels
open CryptoLib
open LabeledCryptoAPI

(*! Note: Most of this file is auto-generated, do not touch by hand *)

let concat3 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 b3))

let split3 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, b3) -> Success (b1, b2, b3)
  )

let parse3_split3_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l)
  : Lemma (split3 #p #i #l (concat3 #p #i #l b1 b2 b3) == Success (b1, b2, b3))
  [SMTPat (split3 #p #i #l (concat3 #p #i #l b1 b2 b3))] = ()

let split_raw3 (t1:bytes) : result (bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, b3) -> Success (b1, b2, b3)
  )

let parse3_split_raw3_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l)
  : Lemma (split_raw3 (concat3 #p #i #l b1 b2 b3) == Success (b1, b2, b3))
  [SMTPat (split_raw3 (concat3 #p #i #l b1 b2 b3))] = ()

let split3_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split3 #p #i #l t in
    let raw_res = split_raw3 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3) = res in
      let Success (br1, br2, br3) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3
    ))
  )
  [SMTPat (split_raw3 t); SMTPat (split3 #p #i #l t)] = ()

let concat4 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 (concat #p #i #l b3 b4)))

let split4 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match split #p #i #l t3 with
      | Error e -> Error e
      | Success (b3, b4) -> Success (b1, b2, b3, b4)
    )
  )

let parse4_split4_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l)
  : Lemma (split4 #p #i #l (concat4 #p #i #l b1 b2 b3 b4) == Success (b1, b2, b3, b4))
  [SMTPat (split4 #p #i #l (concat4 #p #i #l b1 b2 b3 b4))] = ()

let split_raw4 (t1:bytes) : result (bytes & bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match CryptoLib.split t3 with
      | Error e -> Error e
      | Success (b3, b4) -> Success (b1, b2, b3, b4)
    )
  )

let parse4_split_raw4_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l)
  : Lemma (split_raw4 (concat4 #p #i #l b1 b2 b3 b4) == Success (b1, b2, b3, b4))
  [SMTPat (split_raw4 (concat4 #p #i #l b1 b2 b3 b4))] = ()

let split4_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split4 #p #i #l t in
    let raw_res = split_raw4 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3, b4) = res in
      let Success (br1, br2, br3, br4) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3 /\ b4 == br4
    ))
  )
  [SMTPat (split_raw4 t); SMTPat (split4 #p #i #l t)] = ()

let concat5 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 (concat #p #i #l b3 (concat #p #i #l b4 b5))))

let split5 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match split #p #i #l t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match split #p #i #l t4 with
        | Error e -> Error e
        | Success (b4, b5) -> Success (b1, b2, b3, b4, b5)
      )
    )
  )

let parse5_split5_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l)
  : Lemma (split5 #p #i #l (concat5 #p #i #l b1 b2 b3 b4 b5) == Success (b1, b2, b3, b4, b5))
  [SMTPat (split5 #p #i #l (concat5 #p #i #l b1 b2 b3 b4 b5))] = ()

let split_raw5 (t1:bytes) : result (bytes & bytes & bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match CryptoLib.split t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match CryptoLib.split t4 with
        | Error e -> Error e
        | Success (b4, b5) -> Success (b1, b2, b3, b4, b5)
      )
    )
  )

let parse5_split_raw5_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l)
  : Lemma (split_raw5 (concat5 #p #i #l b1 b2 b3 b4 b5) == Success (b1, b2, b3, b4, b5))
  [SMTPat (split_raw5 (concat5 #p #i #l b1 b2 b3 b4 b5))] = ()

let split5_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split5 #p #i #l t in
    let raw_res = split_raw5 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3, b4, b5) = res in
      let Success (br1, br2, br3, br4, br5) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3 /\ b4 == br4 /\ b5 == br5
    ))
  )
  [SMTPat (split_raw5 t); SMTPat (split5 #p #i #l t)] = ()

let concat6 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 (concat #p #i #l b3 (concat #p #i #l b4 (concat #p #i #l b5 b6)))))

let split6 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match split #p #i #l t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match split #p #i #l t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match split #p #i #l t5 with
          | Error e -> Error e
          | Success (b5, b6) -> Success (b1, b2, b3, b4, b5, b6)
        )
      )
    )
  )

let parse6_split6_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l)
  : Lemma (split6 #p #i #l (concat6 #p #i #l b1 b2 b3 b4 b5 b6) == Success (b1, b2, b3, b4, b5, b6))
  [SMTPat (split6 #p #i #l (concat6 #p #i #l b1 b2 b3 b4 b5 b6))] = ()

let split_raw6 (t1:bytes) : result (bytes & bytes & bytes & bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match CryptoLib.split t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match CryptoLib.split t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match CryptoLib.split t5 with
          | Error e -> Error e
          | Success (b5, b6) -> Success (b1, b2, b3, b4, b5, b6)
        )
      )
    )
  )

let parse6_split_raw6_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l)
  : Lemma (split_raw6 (concat6 #p #i #l b1 b2 b3 b4 b5 b6) == Success (b1, b2, b3, b4, b5, b6))
  [SMTPat (split_raw6 (concat6 #p #i #l b1 b2 b3 b4 b5 b6))] = ()

let split6_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split6 #p #i #l t in
    let raw_res = split_raw6 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3, b4, b5, b6) = res in
      let Success (br1, br2, br3, br4, br5, br6) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3 /\ b4 == br4 /\ b5 == br5 /\ b6 == br6
    ))
  )
  [SMTPat (split_raw6 t); SMTPat (split6 #p #i #l t)] = ()

let concat7 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 (concat #p #i #l b3 (concat #p #i #l b4 (concat #p #i #l b5 (concat #p #i #l b6 b7))))))

let split7 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match split #p #i #l t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match split #p #i #l t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match split #p #i #l t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match split #p #i #l t6 with
            | Error e -> Error e
            | Success (b6, b7) -> Success (b1, b2, b3, b4, b5, b6, b7)
          )
        )
      )
    )
  )

let parse7_split7_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l)
  : Lemma (split7 #p #i #l (concat7 #p #i #l b1 b2 b3 b4 b5 b6 b7) == Success (b1, b2, b3, b4, b5, b6, b7))
  [SMTPat (split7 #p #i #l (concat7 #p #i #l b1 b2 b3 b4 b5 b6 b7))] = ()

let split_raw7 (t1:bytes) : result (bytes & bytes & bytes & bytes & bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match CryptoLib.split t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match CryptoLib.split t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match CryptoLib.split t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match CryptoLib.split t6 with
            | Error e -> Error e
            | Success (b6, b7) -> Success (b1, b2, b3, b4, b5, b6, b7)
          )
        )
      )
    )
  )

let parse7_split_raw7_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l)
  : Lemma (split_raw7 (concat7 #p #i #l b1 b2 b3 b4 b5 b6 b7) == Success (b1, b2, b3, b4, b5, b6, b7))
  [SMTPat (split_raw7 (concat7 #p #i #l b1 b2 b3 b4 b5 b6 b7))] = ()

let split7_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split7 #p #i #l t in
    let raw_res = split_raw7 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3, b4, b5, b6, b7) = res in
      let Success (br1, br2, br3, br4, br5, br6, br7) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3 /\ b4 == br4 /\ b5 == br5 /\ b6 == br6 /\ b7 == br7
    ))
  )
  [SMTPat (split_raw7 t); SMTPat (split7 #p #i #l t)] = ()

let concat8 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 (concat #p #i #l b3 (concat #p #i #l b4 (concat #p #i #l b5 (concat #p #i #l b6 (concat #p #i #l b7 b8)))))))

let split8 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match split #p #i #l t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match split #p #i #l t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match split #p #i #l t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match split #p #i #l t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match split #p #i #l t7 with
              | Error e -> Error e
              | Success (b7, b8) -> Success (b1, b2, b3, b4, b5, b6, b7, b8)
            )
          )
        )
      )
    )
  )

let parse8_split8_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l)
  : Lemma (split8 #p #i #l (concat8 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8) == Success (b1, b2, b3, b4, b5, b6, b7, b8))
  [SMTPat (split8 #p #i #l (concat8 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8))] = ()

let split_raw8 (t1:bytes) : result (bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match CryptoLib.split t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match CryptoLib.split t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match CryptoLib.split t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match CryptoLib.split t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match CryptoLib.split t7 with
              | Error e -> Error e
              | Success (b7, b8) -> Success (b1, b2, b3, b4, b5, b6, b7, b8)
            )
          )
        )
      )
    )
  )

let parse8_split_raw8_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l)
  : Lemma (split_raw8 (concat8 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8) == Success (b1, b2, b3, b4, b5, b6, b7, b8))
  [SMTPat (split_raw8 (concat8 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8))] = ()

let split8_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split8 #p #i #l t in
    let raw_res = split_raw8 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3, b4, b5, b6, b7, b8) = res in
      let Success (br1, br2, br3, br4, br5, br6, br7, br8) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3 /\ b4 == br4 /\ b5 == br5 /\ b6 == br6 /\ b7 == br7 /\ b8 == br8
    ))
  )
  [SMTPat (split_raw8 t); SMTPat (split8 #p #i #l t)] = ()

let concat9 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 (concat #p #i #l b3 (concat #p #i #l b4 (concat #p #i #l b5 (concat #p #i #l b6 (concat #p #i #l b7 (concat #p #i #l b8 b9))))))))

let split9 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match split #p #i #l t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match split #p #i #l t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match split #p #i #l t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match split #p #i #l t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match split #p #i #l t7 with
              | Error e -> Error e
              | Success (b7, t8) -> (
                match split #p #i #l t8 with
                | Error e -> Error e
                | Success (b8, b9) -> Success (b1, b2, b3, b4, b5, b6, b7, b8, b9)
              )
            )
          )
        )
      )
    )
  )

let parse9_split9_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l)
  : Lemma (split9 #p #i #l (concat9 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9) == Success (b1, b2, b3, b4, b5, b6, b7, b8, b9))
  [SMTPat (split9 #p #i #l (concat9 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9))] = ()

let split_raw9 (t1:bytes) : result (bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match CryptoLib.split t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match CryptoLib.split t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match CryptoLib.split t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match CryptoLib.split t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match CryptoLib.split t7 with
              | Error e -> Error e
              | Success (b7, t8) -> (
                match CryptoLib.split t8 with
                | Error e -> Error e
                | Success (b8, b9) -> Success (b1, b2, b3, b4, b5, b6, b7, b8, b9)
              )
            )
          )
        )
      )
    )
  )

let parse9_split_raw9_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l)
  : Lemma (split_raw9 (concat9 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9) == Success (b1, b2, b3, b4, b5, b6, b7, b8, b9))
  [SMTPat (split_raw9 (concat9 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9))] = ()

let split9_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split9 #p #i #l t in
    let raw_res = split_raw9 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3, b4, b5, b6, b7, b8, b9) = res in
      let Success (br1, br2, br3, br4, br5, br6, br7, br8, br9) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3 /\ b4 == br4 /\ b5 == br5 /\ b6 == br6 /\ b7 == br7 /\ b8 == br8 /\ b9 == br9
    ))
  )
  [SMTPat (split_raw9 t); SMTPat (split9 #p #i #l t)] = ()


let concat10 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) (b10:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 (concat #p #i #l b3 (concat #p #i #l b4 (concat #p #i #l b5 (concat #p #i #l b6 (concat #p #i #l b7 (concat #p #i #l b8 (concat #p #i #l b9 b10)))))))))

let split10 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match split #p #i #l t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match split #p #i #l t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match split #p #i #l t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match split #p #i #l t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match split #p #i #l t7 with
              | Error e -> Error e
              | Success (b7, t8) -> (
                match split #p #i #l t8 with
                | Error e -> Error e
                | Success (b8, t9) -> (
                  match split #p #i #l t9 with
                  | Error e -> Error e
                  | Success (b9, b10) -> Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)
                )
              )
            )
          )
        )
      )
    )
  )

let parse10_split10_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) (b10:msg p i l)
  : Lemma (split10 #p #i #l (concat10 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10) == Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10))
  [SMTPat (split10 #p #i #l (concat10 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10))] = ()

let split_raw10 (t1:bytes) : result (bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match CryptoLib.split t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match CryptoLib.split t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match CryptoLib.split t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match CryptoLib.split t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match CryptoLib.split t7 with
              | Error e -> Error e
              | Success (b7, t8) -> (
                match CryptoLib.split t8 with
                | Error e -> Error e
                | Success (b8, t9) -> (
                  match CryptoLib.split t9 with
                  | Error e -> Error e
                  | Success (b9, b10) -> Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)
                )
              )
            )
          )
        )
      )
    )
  )

let parse10_split_raw10_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) (b10:msg p i l)
  : Lemma (split_raw10 (concat10 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10) == Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10))
  [SMTPat (split_raw10 (concat10 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10))] = ()

let split10_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split10 #p #i #l t in
    let raw_res = split_raw10 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10) = res in
      let Success (br1, br2, br3, br4, br5, br6, br7, br8, br9, br10) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3 /\ b4 == br4 /\ b5 == br5 /\ b6 == br6 /\ b7 == br7 /\ b8 == br8 /\ b9 == br9 /\ b10 == br10
    ))
  )
  [SMTPat (split_raw10 t); SMTPat (split10 #p #i #l t)] = ()


let concat11 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) (b10:msg p i l) (b11:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 (concat #p #i #l b3 (concat #p #i #l b4 (concat #p #i #l b5 (concat #p #i #l b6 (concat #p #i #l b7 (concat #p #i #l b8 (concat #p #i #l b9 (concat #p #i #l b10 b11))))))))))

let split11 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match split #p #i #l t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match split #p #i #l t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match split #p #i #l t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match split #p #i #l t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match split #p #i #l t7 with
              | Error e -> Error e
              | Success (b7, t8) -> (
                match split #p #i #l t8 with
                | Error e -> Error e
                | Success (b8, t9) -> (
                  match split #p #i #l t9 with
                  | Error e -> Error e
                  | Success (b9, t10) -> (
                    match split #p #i #l t10 with
                    | Error e -> Error e
                    | Success (b10, b11) -> Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11)
                  )
                )
              )
            )
          )
        )
      )
    )
  )

let parse11_split11_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) (b10:msg p i l) (b11:msg p i l)
  : Lemma (split11 #p #i #l (concat11 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11) == Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11))
  [SMTPat (split11 #p #i #l (concat11 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11))] = ()

let split_raw11 (t1:bytes) : result (bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match CryptoLib.split t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match CryptoLib.split t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match CryptoLib.split t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match CryptoLib.split t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match CryptoLib.split t7 with
              | Error e -> Error e
              | Success (b7, t8) -> (
                match CryptoLib.split t8 with
                | Error e -> Error e
                | Success (b8, t9) -> (
                  match CryptoLib.split t9 with
                  | Error e -> Error e
                  | Success (b9, t10) -> (
                    match CryptoLib.split t10 with
                    | Error e -> Error e
                    | Success (b10, b11) -> Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11)
                  )
                )
              )
            )
          )
        )
      )
    )
  )

let parse11_split_raw11_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) (b10:msg p i l) (b11:msg p i l)
  : Lemma (split_raw11 (concat11 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11) == Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11))
  [SMTPat (split_raw11 (concat11 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11))] = ()

let split11_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split11 #p #i #l t in
    let raw_res = split_raw11 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11) = res in
      let Success (br1, br2, br3, br4, br5, br6, br7, br8, br9, br10, br11) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3 /\ b4 == br4 /\ b5 == br5 /\ b6 == br6 /\ b7 == br7 /\ b8 == br8 /\ b9 == br9 /\ b10 == br10 /\ b11 == br11
    ))
  )
  [SMTPat (split_raw11 t); SMTPat (split11 #p #i #l t)] = ()


let concat12 (#p:global_usage) (#i:timestamp) (#l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) (b10:msg p i l) (b11:msg p i l) (b12:msg p i l) : (b:msg p i l) =
  (concat #p #i #l b1 (concat #p #i #l b2 (concat #p #i #l b3 (concat #p #i #l b4 (concat #p #i #l b5 (concat #p #i #l b6 (concat #p #i #l b7 (concat #p #i #l b8 (concat #p #i #l b9 (concat #p #i #l b10 (concat #p #i #l b11 b12)))))))))))

let split12 (#p:global_usage) (#i:timestamp) (#l:label) (t1:msg p i l) : result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l) =
  match split #p #i #l t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match split #p #i #l t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match split #p #i #l t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match split #p #i #l t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match split #p #i #l t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match split #p #i #l t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match split #p #i #l t7 with
              | Error e -> Error e
              | Success (b7, t8) -> (
                match split #p #i #l t8 with
                | Error e -> Error e
                | Success (b8, t9) -> (
                  match split #p #i #l t9 with
                  | Error e -> Error e
                  | Success (b9, t10) -> (
                    match split #p #i #l t10 with
                    | Error e -> Error e
                    | Success (b10, t11) -> (
                      match split #p #i #l t11 with
                      | Error e -> Error e
                      | Success (b11, b12) -> Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12)
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

let parse12_split12_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) (b10:msg p i l) (b11:msg p i l) (b12:msg p i l)
  : Lemma (split12 #p #i #l (concat12 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12) == Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12))
  [SMTPat (split12 #p #i #l (concat12 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12))] = ()

let split_raw12 (t1:bytes) : result (bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes & bytes) =
  match CryptoLib.split t1 with
  | Error e -> Error e
  | Success (b1, t2) -> (
    match CryptoLib.split t2 with
    | Error e -> Error e
    | Success (b2, t3) -> (
      match CryptoLib.split t3 with
      | Error e -> Error e
      | Success (b3, t4) -> (
        match CryptoLib.split t4 with
        | Error e -> Error e
        | Success (b4, t5) -> (
          match CryptoLib.split t5 with
          | Error e -> Error e
          | Success (b5, t6) -> (
            match CryptoLib.split t6 with
            | Error e -> Error e
            | Success (b6, t7) -> (
              match CryptoLib.split t7 with
              | Error e -> Error e
              | Success (b7, t8) -> (
                match CryptoLib.split t8 with
                | Error e -> Error e
                | Success (b8, t9) -> (
                  match CryptoLib.split t9 with
                  | Error e -> Error e
                  | Success (b9, t10) -> (
                    match CryptoLib.split t10 with
                    | Error e -> Error e
                    | Success (b10, t11) -> (
                      match CryptoLib.split t11 with
                      | Error e -> Error e
                      | Success (b11, b12) -> Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12)
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

let parse12_split_raw12_lemma (p:global_usage) (i:timestamp) (l:label) (b1:msg p i l) (b2:msg p i l) (b3:msg p i l) (b4:msg p i l) (b5:msg p i l) (b6:msg p i l) (b7:msg p i l) (b8:msg p i l) (b9:msg p i l) (b10:msg p i l) (b11:msg p i l) (b12:msg p i l)
  : Lemma (split_raw12 (concat12 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12) == Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12))
  [SMTPat (split_raw12 (concat12 #p #i #l b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12))] = ()

let split12_eq_lemma (p:global_usage) (i:timestamp) (l:label) (t:msg p i l)
  : Lemma (
    let res = split12 #p #i #l t in
    let raw_res = split_raw12 t in
    (Success? res <==> Success? raw_res) /\
    (Success? res ==> (
      let Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12) = res in
      let Success (br1, br2, br3, br4, br5, br6, br7, br8, br9, br10, br11, br12) = raw_res in
      b1 == br1 /\ b2 == br2 /\ b3 == br3 /\ b4 == br4 /\ b5 == br5 /\ b6 == br6 /\ b7 == br7 /\ b8 == br8 /\ b9 == br9 /\ b10 == br10 /\ b11 == br11 /\ b12 == br12
    ))
  )
  [SMTPat (split_raw12 t); SMTPat (split12 #p #i #l t)] = ()



/// Since the do-notation is deprecated and monadic let does not seem to work, we use this "manual
/// bind" for now.
let bsplit_raw (#a:Type) (b:bytes) (f:bytes -> bytes -> result a) : result a =
  let? (b1,b2) = CryptoLib.split b in
  f b1 b2

let bsplit_raw3 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> result a) : result a =
  match split_raw3 b with
  | Error e -> Error e
  | Success (b1, b2, b3) -> f b1 b2 b3

let bsplit_raw4 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> bytes -> result a) : result a =
  match split_raw4 b with
  | Error e -> Error e
  | Success (b1, b2, b3, b4) -> f b1 b2 b3 b4

let bsplit_raw5 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> bytes -> bytes -> result a) : result a =
  match split_raw5 b with
  | Error e -> Error e
  | Success (b1, b2, b3, b4, b5) -> f b1 b2 b3 b4 b5

let bsplit_raw6 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> result a) : result a =
  match split_raw6 b with
  | Error e -> Error e
  | Success (b1, b2, b3, b4, b5, b6) -> f b1 b2 b3 b4 b5 b6

let bsplit_raw7 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> result a) : result a =
  match split_raw7 b with
  | Error e -> Error e
  | Success (b1, b2, b3, b4, b5, b6, b7) -> f b1 b2 b3 b4 b5 b6 b7

let bsplit_raw8 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> result a) : result a =
  match split_raw8 b with
  | Error e -> Error e
  | Success (b1, b2, b3, b4, b5, b6, b7, b8) -> f b1 b2 b3 b4 b5 b6 b7 b8

let bsplit_raw9 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> result a) : result a =
  match split_raw9 b with
  | Error e -> Error e
  | Success (b1, b2, b3, b4, b5, b6, b7, b8, b9) -> f b1 b2 b3 b4 b5 b6 b7 b8 b9

let bsplit_raw10 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> result a) : result a =
  match split_raw10 b with
  | Error e -> Error e
  | Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10) -> f b1 b2 b3 b4 b5 b6 b7 b8 b9 b10

let bsplit_raw11 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> result a) : result a =
  match split_raw11 b with
  | Error e -> Error e
  | Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11) -> f b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11

let bsplit_raw12 (#a:Type) (b:bytes) (f:bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> result a) : result a =
  match split_raw12 b with
  | Error e -> Error e
  | Success (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12) -> f b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12

/// Labeled Crypto Functions as Record
/// ==================================
/// 
/// Type for a set of labeled crypto functions, to avoid having to pass usage, timestamp, and label
/// everytime.
noeq type labeled_crypto_funs_t (p:global_usage) (i:timestamp) (l:label) = {
  empty: lbytes p i public;
  bool_to_bytes: bool -> Tot (lbytes p i public);
  bytes_to_bool: msg p i l -> result bool;
  string_to_bytes: string -> Tot (lbytes p i public);
  bytes_to_string: msg p i l -> result string;
  nat_to_bytes: nat -> Tot (lbytes p i public);
  bytes_to_nat: msg p i l -> result nat;
  concat: b1:msg p i l -> b2:msg p i l -> b:msg p i l{get_label p.key_usages b == meet (get_label p.key_usages b1) (get_label p.key_usages b2)};
  split: msg p i l -> result (msg p i l & msg p i l);
  concat3: msg p i l -> msg p i l -> msg p i l -> msg p i l;
  concat4: msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l;
  concat5: msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l;
  concat6: msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l;
  concat7: msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l;
  concat8: msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l;
  concat9: msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l;
  concat10: msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l;
  concat11: msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l;
  concat12: msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l -> msg p i l;
  split3: msg p i l -> result (msg p i l & msg p i l & msg p i l);
  split4: msg p i l -> result (msg p i l & msg p i l & msg p i l & msg p i l);
  split5: msg p i l -> result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l);
  split6: msg p i l -> result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l);
  split7: msg p i l -> result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l);
  split8: msg p i l -> result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l);
  split9: msg p i l -> result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l);
  split10: msg p i l -> result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l);
  split11: msg p i l -> result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l);
  split12: msg p i l -> result (msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l & msg p i l);
}

/// Function to create a ``labeled_crypto_funs_t``
let labeled_crypto_funs (gu:global_usage) (i:timestamp) (l:label): labeled_crypto_funs_t gu i l = {
  empty = LabeledCryptoAPI.empty #gu #i;
  bool_to_bytes = LabeledCryptoAPI.bool_to_bytes #gu #i;
  bytes_to_bool = LabeledCryptoAPI.bytes_to_bool #gu #i #l;
  string_to_bytes = LabeledCryptoAPI.string_to_bytes #gu #i;
  bytes_to_string = LabeledCryptoAPI.bytes_to_string #gu #i #l;
  nat_to_bytes = LabeledCryptoAPI.nat_to_bytes #gu #i 0;
  bytes_to_nat = LabeledCryptoAPI.bytes_to_nat #gu #i #l;
  concat = LabeledCryptoAPI.concat #gu #i #l;
  split = LabeledCryptoAPI.split #gu #i #l;
  concat3 = concat3 #gu #i #l;
  concat4 = concat4 #gu #i #l;
  concat5 = concat5 #gu #i #l;
  concat6 = concat6 #gu #i #l;
  concat7 = concat7 #gu #i #l;
  concat8 = concat8 #gu #i #l;
  concat9 = concat9 #gu #i #l;
  concat10 = concat10 #gu #i #l;
  concat11 = concat11 #gu #i #l;
  concat12 = concat12 #gu #i #l;
  split3 = split3 #gu #i #l;
  split4 = split4 #gu #i #l;
  split5 = split5 #gu #i #l;
  split6 = split6 #gu #i #l;
  split7 = split7 #gu #i #l;
  split8 = split8 #gu #i #l;
  split9 = split9 #gu #i #l;
  split10 = split10 #gu #i #l;
  split11 = split11 #gu #i #l;
  split12 = split12 #gu #i #l;
}


/// Serialization/Parsing for some common data types
/// ================================================
///
/// Optional ``bytes``
/// ------------------
let serialize_opt_bytes (#gu:global_usage) (#i:timestamp) (#l:label) (m:option bytes{Some? m ==> is_msg gu i (Some?.v m) l}) : msg gu i l =
  let c = labeled_crypto_funs gu i l in
  if None? m then
    c.concat (c.string_to_bytes "Opt:None") c.empty
  else
    c.concat (c.string_to_bytes "Opt:Some") (Some?.v m)

let parse_opt_bytes_ (#gu:global_usage) (#i:timestamp) (#l:label) (m:msg gu i l) : (r:result (option (t:bytes{is_msg gu i t l}))) =
  let c = labeled_crypto_funs gu i l in
  match c.split m with
  | Error e -> Error e
  | Success (str, v) ->
  match c.bytes_to_string str with
  | Success "Opt:None" -> if v = c.empty then Success None else Error "Not an option bytes"
  | Success "Opt:Some" -> Success (Some (v <: t:bytes{is_msg gu i t l}))
  | _ -> Error "Not an option bytes"

let is_msg_in_result_opt (gu:global_usage) (i:timestamp) (l:label) (r:result (option bytes)) : Type =
  match r with
  | Success (Some t) -> is_msg gu i t l
  | _ -> True

let parse_opt_bytes (#gu:global_usage) (#i:timestamp) (#l:label) (m:msg gu i l) : (r:result (option bytes){is_msg_in_result_opt gu i l r}) =
  match parse_opt_bytes_ #gu #i #l m with
  | Success None -> Success None
  | Error e -> Error e
  | Success (Some v) -> Success (Some v)

let parse_opt_bytes_raw (m:bytes) : result (option bytes) =
  match CryptoLib.split m with
  | Error e -> Error e
  | Success (str, v) ->
  match CryptoLib.bytes_to_string str with
  | Success "Opt:None" -> if v = CryptoLib.empty then Success None else Error "Not an option bytes"
  | Success "Opt:Some" -> Success (Some v)
  | _ -> Error "Not an option bytes"

let parse_serialize_opt_bytes_lemma #gu #i #l m
  : Lemma (
    let r = parse_opt_bytes #gu #i #l (serialize_opt_bytes #gu #i #l m) in
    let r2 = parse_opt_bytes_raw (serialize_opt_bytes #gu #i #l m) in
    match r with
    | Error _ -> False
    | Success m' -> m == m' /\ r == r2
  )
  [SMTPatOr [[SMTPat (parse_opt_bytes #gu #i #l (serialize_opt_bytes #gu #i #l m))];
             [SMTPat (parse_opt_bytes_raw (serialize_opt_bytes #gu #i #l m))]]]
  = ()

/// "Constructors" for additional serialization/parsing of optional values
/// ----------------------------------------------------------------------
let serialize_opt_a (#a:Type) (gu:global_usage) (i:timestamp) (l:label) (serialize_a:a -> msg gu i l) (v:option a) : (r:msg gu i l) =
  match v with
  | None -> serialize_opt_bytes #gu #i #l None
  | Some va -> serialize_opt_bytes #gu #i #l (Some (serialize_a va))

let parse_opt_a (#a:Type) (gu:global_usage) (i:timestamp) (l:label) (parse_a:msg gu i l -> result a) (m:msg gu i l) : (r:result (option a)) =
  match parse_opt_bytes #gu #i #l m with
  | Success (Some a_bytes) -> (
    match parse_a a_bytes with
    | Success a_val -> Success (Some a_val)
    | Error e -> Error e
  )
  | Success None -> Success None
  | _ -> Error "parse_opt_a: Not an option bytes"

let parse_opt_raw_a (#a:Type) (parse_raw_a:bytes -> result a) (m:bytes) : (r:result (option a)) =
  match parse_opt_bytes_raw m with
  | Success (Some a_bytes) -> (
    match parse_raw_a a_bytes with
    | Success a_val -> Success (Some a_val)
    | Error e -> Error e
  )
  | Success None -> Success None
  | _ -> Error "parse_opt_raw_a: Not an option bytes"

/// Optional ``string``
/// -------------------
let serialize_opt_string (#gu:global_usage) (#i:timestamp) (#l:label) (s:option string) : msg gu i l =
  serialize_opt_a gu i l (LabeledCryptoAPI.string_to_bytes #gu #i) s

let parse_opt_string (#gu:global_usage) (#i:timestamp) (#l:label) (m:msg gu i l) : (r:result (option string)) =
  parse_opt_a gu i l (LabeledCryptoAPI.bytes_to_string #gu #i #l) m

let parse_opt_string_raw (m:bytes) : (r:result (option string)) =
  parse_opt_raw_a CryptoLib.bytes_to_string m

let parse_serialize_opt_string_lemma #gu #i #l m
  : Lemma (
    let r = parse_opt_string #gu #i #l (serialize_opt_string #gu #i #l m) in
    let r2 = parse_opt_string_raw (serialize_opt_string #gu #i #l m) in
    match r with
    | Error _ -> False
    | Success m' -> m == m' /\ r == r2
  )
  [SMTPatOr [[SMTPat (parse_opt_string #gu #i #l (serialize_opt_string #gu #i #l m))];
             [SMTPat (parse_opt_string_raw (serialize_opt_string #gu #i #l m))]]]
  = ()


/// Optional ``bool``
/// -----------------
let serialize_opt_bool (#gu:global_usage) (#i:timestamp) (#l:label) (b_opt:option bool): msg gu i l =
  serialize_opt_a gu i l (LabeledCryptoAPI.bool_to_bytes #gu #i) b_opt

let parse_opt_bool (#gu:global_usage) (#i:timestamp) (#l:label) (m:msg gu i l) : (r:result (option bool)) =
  parse_opt_a gu i l (LabeledCryptoAPI.bytes_to_bool #gu #i #l) m

let parse_opt_bool_raw (m:bytes) : (r:result (option bool)) =
  parse_opt_raw_a CryptoLib.bytes_to_bool m

let parse_serialize_opt_bool_lemma #gu #i #l m
  : Lemma (
    let r = parse_opt_bool #gu #i #l (serialize_opt_bool #gu #i #l m) in
    let r2 = parse_opt_bool_raw (serialize_opt_bool #gu #i #l m) in
    match r with
    | Error _ -> False
    | Success m' -> m == m' /\ r == r2
  )
  [SMTPatOr [[SMTPat (parse_opt_bool #gu #i #l (serialize_opt_bool #gu #i #l m))];
             [SMTPat (parse_opt_bool_raw (serialize_opt_bool #gu #i #l m))]]]
  = ()


/// Optional ``nat``
/// -----------------
let serialize_opt_nat (#gu:global_usage) (#i:timestamp) (#l:label) (b_opt:option nat): msg gu i l =
  serialize_opt_a gu i l (LabeledCryptoAPI.nat_to_bytes #gu #i 0) b_opt

let parse_opt_nat (#gu:global_usage) (#i:timestamp) (#l:label) (m:msg gu i l) : (r:result (option nat)) =
  parse_opt_a gu i l (LabeledCryptoAPI.bytes_to_nat #gu #i #l) m

let parse_opt_nat_raw (m:bytes) : (r:result (option nat)) =
  parse_opt_raw_a CryptoLib.bytes_to_nat m

let parse_serialize_opt_nat_lemma #gu #i #l m
  : Lemma (
    let r = parse_opt_nat #gu #i #l (serialize_opt_nat #gu #i #l m) in
    let r2 = parse_opt_nat_raw (serialize_opt_nat #gu #i #l m) in
    match r with
    | Error _ -> False
    | Success m' -> m == m' /\ r == r2
  )
  [SMTPatOr [[SMTPat (parse_opt_nat #gu #i #l (serialize_opt_nat #gu #i #l m))];
             [SMTPat (parse_opt_nat_raw (serialize_opt_nat #gu #i #l m))]]]
  = ()
