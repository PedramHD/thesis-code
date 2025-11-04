Basic Authentication Example
=============================

A simple basic authentication protocol to demonstrate the communication module.

The protocol between a client :math:`C` and a server :math:`S` commences as follows with :math:`\{\cdot\}^{\text{authN}(p)}_{\text{conf}}` denoting a channel to party :math:`p` which is authenticated and confidential (think of an HTTPS request), :math:`\{\cdot\}_{\text{conf}}` denoting a confidential channel (think of an HTTPS response), and :math:`n \leftarrow \mathcal{N}` being the generation of a fresh nonce:

.. math::
   C &\colon pw \leftarrow \mathcal{N}, user \leftarrow \text{Strings}\\
   C \to S&\colon \{user, pw\}^{\text{authN}(S)}_{\text{conf}} & \text{(Register new account)}\\
   S &\colon secret \leftarrow \mathcal{N}\\
   S \to C&\colon \{\text{Account created}\}_{\text{conf}} \qquad & \text{(Registration response)}\\
   C \to S&\colon \{user, pw\}^{\text{authN}(S)}_{\text{conf}} & \text{(Request Access)}\\
   S \to C&\colon \{secret\}_{\text{conf}}

.. toctree::
   :maxdepth: 1
   :caption: Contents:
   :glob:

   communication_module/example_basic_authentication/BA.*

