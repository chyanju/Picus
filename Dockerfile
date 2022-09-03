FROM chyanju/picus:base

# copy current version of Eurus
COPY ./ /Picus/

CMD [ "/bin/bash" ]