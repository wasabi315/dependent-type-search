const searchForm = document.querySelector("#search-form");
const searchButton = searchForm.querySelector('button[type="submit"]');

searchForm.addEventListener("submit", () => {
  searchButton.disabled = true;
});

window.addEventListener("pageshow", () => {
  searchButton.disabled = false;
});
