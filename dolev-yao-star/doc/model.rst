Main Model
==========

General Concepts
----------------

TODO DOC write some intro explaining the rough idea etc., including attacker model, how corruption works, usages (why and how)


Overview over the modules
-------------------------

The most important modules for users of DY* are probably the :doc:`LabeledCryptoAPI`, which provides
APIs for cryptographic operations, and the :doc:`LabeledRuntimeAPI`, which provides APIs to interact
with the global state, because protocol models mostly use these APIs.  In addition, some of DY*'s
core concepts are explained throughout the documentation for these modules.  After reading these,
:doc:`LabeledPKI` should be the next module to look at if you're planning on using DY* for protocols
involving public key cryptography (including Diffie-Hellman).

You may also want to take a look at the :doc:`SecurityLemmas` once you try to prove security
properties.

:doc:`AttackerAPI` shows attacker typeability, i.e., proves that the attacker assumptions are
modeled correctly and we do not accidentally restrict the attacker.

The modules :doc:`CryptoLib` and :doc:`GlobalRuntimeLib` are unlabeled versions of the respective
labeled APIs. Together with :doc:`CryptoEffect` and :doc:`SecrecyLabels`, they form the basic
Dolev-Yao model, on top of which we build with trace invariants, labeling, etc.

Quick links to all modules and their implementation
---------------------------------------------------

.. toctree::
   :maxdepth: 1

   AttackerAPI-impl
   AttackerAPI
   CryptoEffect-impl
   CryptoEffect
   symbolic/CryptoLib-impl
   concrete/CryptoLib-impl
   CryptoLib
   GlobalRuntimeLib-impl
   GlobalRuntimeLib
   symbolic/LabeledCryptoAPI-impl
   concrete/LabeledCryptoAPI-impl
   LabeledCryptoAPI
   LabeledPKI-impl
   LabeledPKI
   LabeledRuntimeAPI-impl
   LabeledRuntimeAPI
   SecrecyLabels-impl
   SecrecyLabels
   SecurityLemmas-impl
   SecurityLemmas
   SerializationHelpers-impl
   Ord
   Ord-impl
