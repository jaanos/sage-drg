# Dockerfile for binder
# Reference: https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile

FROM sagemath/sagemath:9.1

# Copy the contents of the repo in ${HOME}
COPY --chown=sage:sage . ${HOME}
RUN sage -pip install RISE==5.6.1
RUN sage -jupyter nbextension install rise --py --sys-prefix
RUN sage -jupyter nbextension enable rise --py --sys-prefix
