FROM veridise/picus:base

# copy current version of Picus
COPY ./ /Picus/

WORKDIR /Picus/
CMD [ "/bin/bash" ]
