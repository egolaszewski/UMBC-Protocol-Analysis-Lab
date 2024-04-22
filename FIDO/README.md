# Artifacts for "Cryptographic Binding Should Not Be Optional: A Formal-Methods Analysis of FIDO UAF Authentication"

This repository contains two different artifacts:

1. CPSA models and outputs for FIDO UAF authentication.
2. Docker images that run an eBay FIDO server and implement a man-in-the-middle attack.

## CPSA

To compile our CPSA models, you require the following software packages:

1. CPSA 3.6.11 [GitHub] (https://hackage.haskell.org/package/cpsa-3.6.11)
2. CPSA 4.4.2 [GitHub] (https://hackage.haskell.org/package/cpsa-4.4.2)
3. GNU Make 4.3

Because of errors in CPSA 4.4.2, we rely on CPSA 3.6.11 for models that involve Diffie-Hellman algebraic
operations and channel binding. The `cpsa3` subdirectory contains two of our models:

uaf-dualbinding-tls13.scm: UAF with our custom dual binding proposal with exporter binding in TLS 1.3.
uaf-exporter-tls13.scm: UAF with the (unsupported) exporter binding using TLS 1.3.

The `cpsa4` subdirectory contains the remaining models:

baseline-nouaf-tls12.scm: Password-based authentication without UAF over TLS 1.2.
uaf-channel-id-tls12.scm: UAF with the channelID binding over TLS 1.2.
uaf-endpoint-tls12.scm: UAF with endpoint binding over TLS 1.2.
uaf-servercert-tls12.scm: UAF with server certificate binding over TLS 1.2.
uaf-token-binding-tls12.scm: UAF with token binding over TLS 1.2.
uaf-unbound-tls12.scm: UAF without channel binding over TLS 1.2.
uaf-ubound-tls13.scm: UAF without channel binding over TLS 1.3.

Our models rely on the following macro files:

TLS1.2_macros.scm
TLS1.3_macros.scm
UAF_macros.scm

To build these models, install CPSA and run `make` in the `cpsa` directory. This command may take several minutes.
For each model, `make` will generate a pair of `xhtml` files: `*.xhtml` and `*_shapes.xhtml`.
The shapes `xhtml` file contains all of the shapes that CPSA finds for each model.

For convenience, we include pre-build artifacts.

## Attack Implementation

This section assumes Docker Desktop 4.19.0 [link](https://www.docker.com/products/docker-desktop/). 

For our attack, we provide a pair of files that define Docker images:

1. `implementation/server/Dockerfile`: Run the eBay FIDO UAF server.
2. `implementation/attack/Dockerfile`: Run a python script modelling our attack.

First, execute the following commands in the `server` directory:
`docker build -t ebay_fido:latest .`
`docker run -p 8080:8080 ebay_fido:latest`

Once the image is running, confirm that you can navigate to `http://localhost:8080/fidouaf/v1/history` and
successfully receive a response.

To test the attack, execute the following commands in the `attack` directory:
`docker build -t ebay_fido_attack:latest .`
`docker run --network="host" ebay_fido_attack:latest`