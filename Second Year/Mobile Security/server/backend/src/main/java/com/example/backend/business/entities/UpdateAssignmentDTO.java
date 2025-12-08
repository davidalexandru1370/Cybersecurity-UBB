package com.example.backend.business.entities;

import java.util.Optional;

public class UpdateAssignmentDTO {
    private String title;
    private String description;
    private Optional<Long> dueDate; // Unix timestamp

    public UpdateAssignmentDTO() {
    }

    public UpdateAssignmentDTO(String title, String description, Optional<Long> dueDate) {
        this.title = title;
        this.description = description;
        this.dueDate = dueDate;
    }

    public String getTitle() {
        return title;
    }

    public void setTitle(String title) {
        this.title = title;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public Optional<Long> getDueDate() {
        return dueDate;
    }

    public void setDueDate(Optional<Long> dueDate) {
        this.dueDate = dueDate;
    }
}
