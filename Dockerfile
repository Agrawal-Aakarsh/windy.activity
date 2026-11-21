# The scorer builds this on linux/amd64 and runs it with no network. The digest is the image the
# commits were labeled in; the selector runs sqlglot's own tests in it, so keep it.
FROM python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90

# What sqlglot's tests need at run time (versions from the kit's requirements.lock). PyPI only.
RUN pip install --no-cache-dir duckdb==2.0.0 pandas==3.1.1 numpy==2.5.5 pytest==9.2.0 \
    python-dateutil==4.0.0 pytz==2026.6 tzdata==2026.6 setuptools==84.2.1

# sqlglot at the pinned commit, from its own repository.
ADD https://github.com/tobymao/sqlglot/archive/eb11aec4be8cb2122afe713a4816662c3f0fb2fa.tar.gz /tmp/sqlglot.tar.gz
RUN mkdir /sqlglot && tar -xzf /tmp/sqlglot.tar.gz -C /sqlglot --strip-components=1 && rm /tmp/sqlglot.tar.gz \
    && python -m compileall -q /sqlglot/sqlglot /sqlglot/tests \
    && chmod -R a+rX /sqlglot

COPY app /app
RUN python -m compileall -q /app && chmod -R a+rX /app

ENV BR_SG=/sqlglot BR_DATA=/data PYTHONDONTWRITEBYTECODE=1 SKIP_INTEGRATION=0
ENV BR_EQUIV=1 BR_PROXY=1 BR_REFINE=1 BR_SELF=1 BR_FIXSLICE=1
CMD ["python", "/app/selector.py"]
