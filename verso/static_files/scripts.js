window.addEventListener('load', function () {
  document.querySelectorAll('.has-info, .warning').forEach(function (el) {
    el.classList.remove('has-info', 'warning');

    el.querySelectorAll('span.hover-container').forEach(function (hoverSpan) {
      hoverSpan.remove();
    });
  });

  document.querySelectorAll('p').forEach(function (p) {
    if (p.querySelector('img')) {
      p.setAttribute('align', 'center');
    }
  });

  document.querySelectorAll('a[href]').forEach(function (link) {
    const url = new URL(link.href, window.location.href);
    if (url.hostname !== window.location.hostname) {
      link.setAttribute('target', '_blank');
      link.setAttribute('rel', 'noopener noreferrer');
    }
  });
});
