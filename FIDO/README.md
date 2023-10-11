# Artifacts for "Cryptographic Binding Should Not Be Optional: A Formal-Methods Analysis of FIDO UAF Authentication"

This repository contains two different artifacts:
1. CPSA models and outputs for FIDO UAF authentication.
2. Docker images that run an eBay FIDO server and implement a man-in-the-middle attack.

## CPSA

To compile our CPSA models, you require the following software packages:
1. CPSA 3.6 [GitHub](https://github.com/mitre/cpsa)
2. GNU Make 4.3

We provide the following models, each implementing an abstraction of a TLS channel binding.
1. fido_no_binding_tls
2. fido_channel_id_binding_tls
3. fido_endpoint_binding_tls
4. fido_server_cert_binding_tls
5. fido_token_binding_tls

For a subset of these channel bindings, we included embedded models that produce simpler shapes.
1. fido_no_binding_embedded
2. fido_channel_id_binding_embedded

Additionally, for the dual binding proposal from the paper, we include a pair of models:
1. fido_dual_binding_tls
2. fido_dual_binding_embedded

To build these models, install CPSA and run `make` in the `cpsa` directory. This command may take several minutes.
For each model, `make` will generate a pair of `xhtml` files: `*.xhtml` and `*_shapes.xhtml`.
The shapes `xhtml` file contains all of the shapes that CPSA finds for each model.

## Attack Implementation

This section assumes Docker Desktop 4.19.0 [link](https://www.docker.com/products/docker-desktop/). 

For our attack, we provide a pair of files that define Docker images:
1. `implementation/server/Dockerfile`: Run the eBay FIDO UAF server.
2. `implementation/attack/Dockerfile`: Run a python script modelling our attack.

First, execute the following commands in the `server` directory:
1. `docker build -t ebay_fido:latest .`
2. `docker run -p 8080:8080 ebay_fido:latest`

Once the image is running, confirm that you can navigate to `http://localhost:8080/fidouaf/v1/history` and
successfully receive a response.

To test the attack, execute the following commands in the `attack` directory:
1. `docker build -t ebay_fido_attack:latest .`
2. `docker run --network="host" ebay_fido_attack:latest`
