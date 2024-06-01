FROM veridise/picus:git-c120fd0437f9488ee73df1a409646d8baede6a2e

# copy current version of Picus
COPY ./ /Picus/

WORKDIR /Picus/
CMD [ "/bin/bash" ]
