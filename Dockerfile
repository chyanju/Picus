FROM chyanju/picus:base.pldi23

# copy current version of Picus
COPY ./ /Picus/

WORKDIR /Picus/
CMD [ "/bin/bash" ]
