# Dockerfile for binder
# Reference: https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile

FROM sagemath/sagemath:8.7

# Copy the contents of the repo in ${HOME}
COPY --chown=sage:sage . ${HOME}
RUN sage -pip install RISE
RUN sage -jupyter nbextension install rise --py --sys-prefix
RUN sage -jupyter nbextension enable rise --py --sys-prefix
RUN cp jupyter/rise-patch/main.js sage/local/share/jupyter/nbextensions/rise/main.js
