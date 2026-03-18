FROM sv-comp:latest

COPY . coar
WORKDIR coar

RUN chmod +x ./setup_coar.sh && ./setup_coar.sh

CMD eval $(opam env) && /bin/bash
