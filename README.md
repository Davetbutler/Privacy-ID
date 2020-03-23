# Privacy-ID

This repo contains the formalisation effort corresponding to the Gates project. 

All the formalisation is done in Isabelle/HOL using the CryptHOL framework. 

To load the framework do the following.

* Download the latest Isabelle version, best ot set an alias isabelle2019 = Isabelle2019/Isabelle2019.app/Isabelle/bin/isabelle 
* Download the latest AFP version (Assume this directory is called afp). 
* Run the following command to load the logic session.
isabelle2019 jedit -d afp/thys/ -l CryptHOL

## Contents of repo

* Multi_Party_Computation contains the formalisation of MPC. Of particular interest to the Gates project is the bidding protocol.
* Privacy_Formalisation contains the initial work in formalising a hierarchy of PETS definitions.



